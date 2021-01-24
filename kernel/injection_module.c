// SPDX-License-Identifier: GPL-2.0-or-later
/*
   Copyright (C) 2002 Richard Henderson
   Copyright (C) 2001 Rusty Russell, 2002, 2010 Rusty Russell IBM.

*/

#define DEBUG
#define pr_fmt(fmt)	"injection_module: " fmt
#define INCLUDE_VERMAGIC

#include <linux/export.h>
#include <linux/extable.h>
#include <linux/moduleloader.h>
#include <linux/module_signature.h>
#include <linux/trace_events.h>
#include <linux/init.h>
#include <linux/kallsyms.h>
#include <linux/file.h>
#include <linux/fs.h>
#include <linux/sysfs.h>
#include <linux/kernel.h>
#include <linux/kernel_read_file.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/elf.h>
#include <linux/proc_fs.h>
#include <linux/security.h>
#include <linux/seq_file.h>
#include <linux/syscalls.h>
#include <linux/fcntl.h>
#include <linux/rcupdate.h>
#include <linux/capability.h>
#include <linux/cpu.h>
#include <linux/moduleparam.h>
#include <linux/errno.h>
#include <linux/err.h>
#include <linux/vermagic.h>
#include <linux/notifier.h>
#include <linux/sched.h>
#include <linux/device.h>
#include <linux/string.h>
#include <linux/mutex.h>
#include <linux/rculist.h>
#include <linux/uaccess.h>
#include <asm/cacheflush.h>
#include <linux/set_memory.h>
#include <asm/mmu_context.h>
#include <linux/license.h>
#include <asm/sections.h>
#include <linux/tracepoint.h>
#include <linux/ftrace.h>
#include <linux/livepatch.h>
#include <linux/async.h>
#include <linux/percpu.h>
#include <linux/kmemleak.h>
#include <linux/jump_label.h>
#include <linux/pfn.h>
#include <linux/bsearch.h>
#include <linux/dynamic_debug.h>
#include <linux/audit.h>
#include <uapi/linux/module.h>

#include "module-internal.h"

#define CREATE_TRACE_POINTS
#include <trace/events/module.h>

#ifndef ARCH_SHF_SMALL
#define ARCH_SHF_SMALL 0
#endif

/*
 * Modules' sections will be aligned on page boundaries
 * to ensure complete separation of code and data, but
 * only when CONFIG_ARCH_HAS_STRICT_MODULE_RWX=y
 */
#ifdef CONFIG_ARCH_HAS_STRICT_MODULE_RWX
# define debug_align(X) ALIGN(X, PAGE_SIZE)
#else
# define debug_align(X) (X)
#endif

/* If this is set, the section belongs in the init part of the module */
#define INIT_OFFSET_MASK (1UL << (BITS_PER_LONG-1))

static LIST_HEAD(injection_modules);

/* Work queue for freeing init sections in success case */
static void do_free_init(struct work_struct *w);
static DECLARE_WORK(init_free_wq, do_free_init);
static LLIST_HEAD(init_free_list);

#ifdef CONFIG_MODULES_TREE_LOOKUP

/*
 * Use a latched RB-tree for __module_address(); this allows us to use
 * RCU-sched lookups of the address from any context.
 *
 * This is conditional on PERF_EVENTS || TRACING because those can really hit
 * __module_address() hard by doing a lot of stack unwinding; potentially from
 * NMI context.
 */

static __always_inline unsigned long __mod_tree_val(struct latch_tree_node *n)
{
	struct module_layout *layout = container_of(n, struct module_layout, mtn.node);

	return (unsigned long)layout->base;
}

static __always_inline unsigned long __mod_tree_size(struct latch_tree_node *n)
{
	struct module_layout *layout = container_of(n, struct module_layout, mtn.node);

	return (unsigned long)layout->size;
}

static __always_inline bool
mod_tree_less(struct latch_tree_node *a, struct latch_tree_node *b)
{
	return __mod_tree_val(a) < __mod_tree_val(b);
}

static __always_inline int
mod_tree_comp(void *key, struct latch_tree_node *n)
{
	unsigned long val = (unsigned long)key;
	unsigned long start, end;

	start = __mod_tree_val(n);
	if (val < start)
		return -1;

	end = start + __mod_tree_size(n);
	if (val >= end)
		return 1;

	return 0;
}

static const struct latch_tree_ops mod_tree_ops = {
	.less = mod_tree_less,
	.comp = mod_tree_comp,
};

static struct mod_tree_root {
	struct latch_tree_root root;
	unsigned long addr_min;
	unsigned long addr_max;
} mod_tree __cacheline_aligned = {
	.addr_min = -1UL,
};

#define module_addr_min mod_tree.addr_min
#define module_addr_max mod_tree.addr_max

static noinline void __mod_tree_insert(struct mod_tree_node *node)
{
	latch_tree_insert(&node->node, &mod_tree.root, &mod_tree_ops);
}

static void __mod_tree_remove(struct mod_tree_node *node)
{
	latch_tree_erase(&node->node, &mod_tree.root, &mod_tree_ops);
}

/*
 * These modifications: insert, remove_init and remove; are serialized by the
 * module_mutex.
 */
static void mod_tree_insert(struct module *mod)
{
	mod->core_layout.mtn.mod = mod;
	mod->init_layout.mtn.mod = mod;

	__mod_tree_insert(&mod->core_layout.mtn);
	if (mod->init_layout.size)
		__mod_tree_insert(&mod->init_layout.mtn);
}

static void mod_tree_remove_init(struct module *mod)
{
	if (mod->init_layout.size)
		__mod_tree_remove(&mod->init_layout.mtn);
}

static void mod_tree_remove(struct module *mod)
{
	__mod_tree_remove(&mod->core_layout.mtn);
	mod_tree_remove_init(mod);
}

#else /* MODULES_TREE_LOOKUP */

static unsigned long module_addr_min = -1UL, module_addr_max = 0;

static void mod_tree_insert(struct module *mod) { }
static void mod_tree_remove_init(struct module *mod) { }
static void mod_tree_remove(struct module *mod) { }

#endif /* MODULES_TREE_LOOKUP */

/*
 * Bounds of module text, for speeding up __module_address.
 * Protected by module_mutex.
 */
static void __mod_update_bounds(void *base, unsigned int size)
{
	unsigned long min = (unsigned long)base;
	unsigned long max = min + size;

	if (min < module_addr_min)
		module_addr_min = min;
	if (max > module_addr_max)
		module_addr_max = max;
}

static void mod_update_bounds(struct module *mod)
{
	__mod_update_bounds(mod->core_layout.base, mod->core_layout.size);
	if (mod->init_layout.size)
		__mod_update_bounds(mod->init_layout.base, mod->init_layout.size);
}

#ifdef CONFIG_KGDB_KDB
struct list_head *kdb_modules = &injection_modules; /* kdb needs the list of modules */
#endif /* CONFIG_KGDB_KDB */

static void module_assert_mutex_or_preempt(void)
{
#ifdef CONFIG_LOCKDEP
	if (unlikely(!debug_locks))
		return;

	WARN_ON_ONCE(!rcu_read_lock_sched_held() &&
		!lockdep_is_held(&module_mutex));
#endif
}

/* Waiting for a module to finish initializing? */
static DECLARE_WAIT_QUEUE_HEAD(module_wq);
static BLOCKING_NOTIFIER_HEAD(module_notify_list);

/*
 * We require a truly strong try_module_get(): 0 means success.
 * Otherwise an error is returned due to ongoing or failed
 * initialization etc.
 */
static inline int strong_try_module_get(struct module *mod)
{
	BUG_ON(mod && mod->state == MODULE_STATE_UNFORMED);
	if (mod && mod->state == MODULE_STATE_COMING)
		return -EBUSY;
	if (try_module_get(mod))
		return 0;
	else
		return -ENOENT;
}

static inline void add_taint_module(struct module *mod, unsigned flag,
				    enum lockdep_ok lockdep_ok)
{
	add_taint(flag, lockdep_ok);
	set_bit(flag, &mod->taints);
}

/* Find a module section: 0 means not found. */
static unsigned int find_sec(const struct load_info *info, const char *name)
{
	unsigned int i;

	for (i = 1; i < info->hdr->e_shnum; i++) {
		Elf_Shdr *shdr = &info->sechdrs[i];
		/* Alloc bit cleared means "ignore it." */
		if ((shdr->sh_flags & SHF_ALLOC)
		    && strcmp(info->secstrings + shdr->sh_name, name) == 0)
			return i;
	}
	return 0;
}

/* Find a module section, or NULL. */
static void *section_addr(const struct load_info *info, const char *name)
{
	/* Section 0 has sh_addr 0. */
	return (void *)info->sechdrs[find_sec(info, name)].sh_addr;
}

/* Find a module section, or NULL.  Fill in number of "objects" in section. */
static void *section_objs(const struct load_info *info,
			  const char *name,
			  size_t object_size,
			  unsigned int *num)
{
	unsigned int sec = find_sec(info, name);

	/* Section 0 has sh_addr 0 and sh_size 0. */
	*num = info->sechdrs[sec].sh_size / object_size;
	return (void *)info->sechdrs[sec].sh_addr;
}

/* Provided by the linker */
extern const struct kernel_symbol __start___ksymtab[];
extern const struct kernel_symbol __stop___ksymtab[];
extern const struct kernel_symbol __start___ksymtab_gpl[];
extern const struct kernel_symbol __stop___ksymtab_gpl[];
extern const struct kernel_symbol __start___ksymtab_gpl_future[];
extern const struct kernel_symbol __stop___ksymtab_gpl_future[];
extern const s32 __start___kcrctab[];
extern const s32 __start___kcrctab_gpl[];
extern const s32 __start___kcrctab_gpl_future[];
#ifdef CONFIG_UNUSED_SYMBOLS
extern const struct kernel_symbol __start___ksymtab_unused[];
extern const struct kernel_symbol __stop___ksymtab_unused[];
extern const struct kernel_symbol __start___ksymtab_unused_gpl[];
extern const struct kernel_symbol __stop___ksymtab_unused_gpl[];
extern const s32 __start___kcrctab_unused[];
extern const s32 __start___kcrctab_unused_gpl[];
#endif

#ifndef CONFIG_MODVERSIONS
#define symversion(base, idx) NULL
#else
#define symversion(base, idx) ((base != NULL) ? ((base) + (idx)) : NULL)
#endif

static bool each_symbol_in_section(const struct symsearch *arr,
				   unsigned int arrsize,
				   struct module *owner,
				   bool (*fn)(const struct symsearch *syms,
					      struct module *owner,
					      void *data),
				   void *data)
{
	unsigned int j;

	for (j = 0; j < arrsize; j++) {
		if (fn(&arr[j], owner, data))
			return true;
	}

	return false;
}

/* Returns true as soon as fn returns true, otherwise false. */
static bool each_symbol_section(bool (*fn)(const struct symsearch *arr,
				    struct module *owner,
				    void *data),
			 void *data)
{
	struct module *mod;
	static const struct symsearch arr[] = {
		{ __start___ksymtab, __stop___ksymtab, __start___kcrctab,
		  NOT_GPL_ONLY, false },
		{ __start___ksymtab_gpl, __stop___ksymtab_gpl,
		  __start___kcrctab_gpl,
		  GPL_ONLY, false },
		{ __start___ksymtab_gpl_future, __stop___ksymtab_gpl_future,
		  __start___kcrctab_gpl_future,
		  WILL_BE_GPL_ONLY, false },
#ifdef CONFIG_UNUSED_SYMBOLS
		{ __start___ksymtab_unused, __stop___ksymtab_unused,
		  __start___kcrctab_unused,
		  NOT_GPL_ONLY, true },
		{ __start___ksymtab_unused_gpl, __stop___ksymtab_unused_gpl,
		  __start___kcrctab_unused_gpl,
		  GPL_ONLY, true },
#endif
	};

	module_assert_mutex_or_preempt();

	if (each_symbol_in_section(arr, ARRAY_SIZE(arr), NULL, fn, data))
		return true;

	list_for_each_entry_rcu(mod, &injection_modules, list,
				lockdep_is_held(&module_mutex)) {
		struct symsearch arr[] = {
			{ mod->syms, mod->syms + mod->num_syms, mod->crcs,
			  NOT_GPL_ONLY, false },
			{ mod->gpl_syms, mod->gpl_syms + mod->num_gpl_syms,
			  mod->gpl_crcs,
			  GPL_ONLY, false },
			{ mod->gpl_future_syms,
			  mod->gpl_future_syms + mod->num_gpl_future_syms,
			  mod->gpl_future_crcs,
			  WILL_BE_GPL_ONLY, false },
#ifdef CONFIG_UNUSED_SYMBOLS
			{ mod->unused_syms,
			  mod->unused_syms + mod->num_unused_syms,
			  mod->unused_crcs,
			  NOT_GPL_ONLY, true },
			{ mod->unused_gpl_syms,
			  mod->unused_gpl_syms + mod->num_unused_gpl_syms,
			  mod->unused_gpl_crcs,
			  GPL_ONLY, true },
#endif
		};

		if (mod->state == MODULE_STATE_UNFORMED)
			continue;

		if (each_symbol_in_section(arr, ARRAY_SIZE(arr), mod, fn, data))
			return true;
	}
	return false;
}

struct find_symbol_arg {
	/* Input */
	const char *name;
	bool gplok;
	bool warn;

	/* Output */
	struct module *owner;
	const s32 *crc;
	const struct kernel_symbol *sym;
	enum mod_license license;
};

static bool check_exported_symbol(const struct symsearch *syms,
				  struct module *owner,
				  unsigned int symnum, void *data)
{
	struct find_symbol_arg *fsa = data;

	if (!fsa->gplok) {
		if (syms->license == GPL_ONLY)
			return false;
		if (syms->license == WILL_BE_GPL_ONLY && fsa->warn) {
			pr_warn("Symbol %s is being used by a non-GPL module, "
				"which will not be allowed in the future\n",
				fsa->name);
		}
	}

#ifdef CONFIG_UNUSED_SYMBOLS
	if (syms->unused && fsa->warn) {
		pr_warn("Symbol %s is marked as UNUSED, however this module is "
			"using it.\n", fsa->name);
		pr_warn("This symbol will go away in the future.\n");
		pr_warn("Please evaluate if this is the right api to use and "
			"if it really is, submit a report to the linux kernel "
			"mailing list together with submitting your code for "
			"inclusion.\n");
	}
#endif

	fsa->owner = owner;
	fsa->crc = symversion(syms->crcs, symnum);
	fsa->sym = &syms->start[symnum];
	fsa->license = syms->license;
	return true;
}

static unsigned long kernel_symbol_value(const struct kernel_symbol *sym)
{
#ifdef CONFIG_HAVE_ARCH_PREL32_RELOCATIONS
	return (unsigned long)offset_to_ptr(&sym->value_offset);
#else
	return sym->value;
#endif
}

static const char *kernel_symbol_name(const struct kernel_symbol *sym)
{
#ifdef CONFIG_HAVE_ARCH_PREL32_RELOCATIONS
	return offset_to_ptr(&sym->name_offset);
#else
	return sym->name;
#endif
}

static const char *kernel_symbol_namespace(const struct kernel_symbol *sym)
{
#ifdef CONFIG_HAVE_ARCH_PREL32_RELOCATIONS
	if (!sym->namespace_offset)
		return NULL;
	return offset_to_ptr(&sym->namespace_offset);
#else
	return sym->namespace;
#endif
}

static int cmp_name(const void *name, const void *sym)
{
	return strcmp(name, kernel_symbol_name(sym));
}

static bool find_exported_symbol_in_section(const struct symsearch *syms,
					    struct module *owner,
					    void *data)
{
	struct find_symbol_arg *fsa = data;
	struct kernel_symbol *sym;

	sym = bsearch(fsa->name, syms->start, syms->stop - syms->start,
			sizeof(struct kernel_symbol), cmp_name);

	if (sym != NULL && check_exported_symbol(syms, owner,
						 sym - syms->start, data))
		return true;

	return false;
}

/* Find an exported symbol and return it, along with, (optional) crc and
 * (optional) module which owns it.  Needs preempt disabled or module_mutex. */
static const struct kernel_symbol *find_symbol(const char *name,
					struct module **owner,
					const s32 **crc,
					enum mod_license *license,
					bool gplok,
					bool warn)
{
	struct find_symbol_arg fsa;

	fsa.name = name;
	fsa.gplok = gplok;
	fsa.warn = warn;

	if (each_symbol_section(find_exported_symbol_in_section, &fsa)) {
		if (owner)
			*owner = fsa.owner;
		if (crc)
			*crc = fsa.crc;
		if (license)
			*license = fsa.license;
		return fsa.sym;
	}

	pr_debug("Failed to find symbol %s\n", name);
	return NULL;
}

/*
 * Search for module by name: must hold module_mutex (or preempt disabled
 * for read-only access).
 */
static struct module *find_module_all(const char *name, size_t len,
				      bool even_unformed)
{
	struct module *mod;

	module_assert_mutex_or_preempt();

	list_for_each_entry_rcu(mod, &injection_modules, list,
				lockdep_is_held(&module_mutex)) {
		if (!even_unformed && mod->state == MODULE_STATE_UNFORMED)
			continue;
		if (strlen(mod->name) == len && !memcmp(mod->name, name, len))
			return mod;
	}
	return NULL;
}

#ifdef CONFIG_SMP

static inline void __percpu *mod_percpu(struct module *mod)
{
	return mod->percpu;
}

static int percpu_modalloc(struct module *mod, struct load_info *info)
{
	Elf_Shdr *pcpusec = &info->sechdrs[info->index.pcpu];
	unsigned long align = pcpusec->sh_addralign;

	if (!pcpusec->sh_size)
		return 0;

	if (align > PAGE_SIZE) {
		pr_warn("%s: per-cpu alignment %li > %li\n",
			mod->name, align, PAGE_SIZE);
		align = PAGE_SIZE;
	}

	mod->percpu = __alloc_reserved_percpu(pcpusec->sh_size, align);
	if (!mod->percpu) {
		pr_warn("%s: Could not allocate %lu bytes percpu data\n",
			mod->name, (unsigned long)pcpusec->sh_size);
		return -ENOMEM;
	}
	mod->percpu_size = pcpusec->sh_size;
	return 0;
}

static void percpu_modfree(struct module *mod)
{
	free_percpu(mod->percpu);
}

static unsigned int find_pcpusec(struct load_info *info)
{
	return find_sec(info, ".data..percpu");
}

static void percpu_modcopy(struct module *mod,
			   const void *from, unsigned long size)
{
	int cpu;

	for_each_possible_cpu(cpu)
		memcpy(per_cpu_ptr(mod->percpu, cpu), from, size);
}

bool __is_module_percpu_address(unsigned long addr, unsigned long *can_addr)
{
	struct module *mod;
	unsigned int cpu;

	preempt_disable();

	list_for_each_entry_rcu(mod, &injection_modules, list) {
		if (mod->state == MODULE_STATE_UNFORMED)
			continue;
		if (!mod->percpu_size)
			continue;
		for_each_possible_cpu(cpu) {
			void *start = per_cpu_ptr(mod->percpu, cpu);
			void *va = (void *)addr;

			if (va >= start && va < start + mod->percpu_size) {
				if (can_addr) {
					*can_addr = (unsigned long) (va - start);
					*can_addr += (unsigned long)
						per_cpu_ptr(mod->percpu,
							    get_boot_cpu_id());
				}
				preempt_enable();
				return true;
			}
		}
	}

	preempt_enable();
	return false;
}

/**
 * is_module_percpu_address - test whether address is from module static percpu
 * @addr: address to test
 *
 * Test whether @addr belongs to module static percpu area.
 *
 * RETURNS:
 * %true if @addr is from module static percpu area
 */
bool is_module_percpu_address(unsigned long addr)
{
	return __is_module_percpu_address(addr, NULL);
}

#else /* ... !CONFIG_SMP */

static inline void __percpu *mod_percpu(struct module *mod)
{
	return NULL;
}
static int percpu_modalloc(struct module *mod, struct load_info *info)
{
	/* UP modules shouldn't have this section: ENOMEM isn't quite right */
	if (info->sechdrs[info->index.pcpu].sh_size != 0)
		return -ENOMEM;
	return 0;
}
static inline void percpu_modfree(struct module *mod)
{
}
static unsigned int find_pcpusec(struct load_info *info)
{
	return 0;
}
static inline void percpu_modcopy(struct module *mod,
				  const void *from, unsigned long size)
{
	/* pcpusec should be 0, and size of that section should be 0. */
	BUG_ON(size != 0);
}
bool is_module_percpu_address(unsigned long addr)
{
	return false;
}

bool __is_module_percpu_address(unsigned long addr, unsigned long *can_addr)
{
	return false;
}

#endif /* CONFIG_SMP */

#define MODINFO_ATTR(field)	\
static void setup_modinfo_##field(struct module *mod, const char *s)  \
{                                                                     \
	mod->field = kstrdup(s, GFP_KERNEL);                          \
}                                                                     \
static ssize_t show_modinfo_##field(struct module_attribute *mattr,   \
			struct module_kobject *mk, char *buffer)      \
{                                                                     \
	return scnprintf(buffer, PAGE_SIZE, "%s\n", mk->mod->field);  \
}                                                                     \
static int modinfo_##field##_exists(struct module *mod)               \
{                                                                     \
	return mod->field != NULL;                                    \
}                                                                     \
static void free_modinfo_##field(struct module *mod)                  \
{                                                                     \
	kfree(mod->field);                                            \
	mod->field = NULL;                                            \
}                                                                     \
static struct module_attribute modinfo_##field = {                    \
	.attr = { .name = __stringify(field), .mode = 0444 },         \
	.show = show_modinfo_##field,                                 \
	.setup = setup_modinfo_##field,                               \
	.test = modinfo_##field##_exists,                             \
	.free = free_modinfo_##field,                                 \
};

MODINFO_ATTR(version);
MODINFO_ATTR(srcversion);

static size_t module_flags_taint(struct module *mod, char *buf)
{
	size_t l = 0;
	int i;

	for (i = 0; i < TAINT_FLAGS_COUNT; i++) {
		if (taint_flags[i].module && test_bit(i, &mod->taints))
			buf[l++] = taint_flags[i].c_true;
	}

	return l;
}

static ssize_t show_initstate(struct module_attribute *mattr,
			      struct module_kobject *mk, char *buffer)
{
	const char *state = "unknown";

	switch (mk->mod->state) {
	case MODULE_STATE_LIVE:
		state = "live";
		break;
	case MODULE_STATE_COMING:
		state = "coming";
		break;
	case MODULE_STATE_GOING:
		state = "going";
		break;
	default:
		BUG();
	}
	return sprintf(buffer, "%s\n", state);
}

static struct module_attribute modinfo_initstate =
	__ATTR(initstate, 0444, show_initstate, NULL);

static ssize_t store_uevent(struct module_attribute *mattr,
			    struct module_kobject *mk,
			    const char *buffer, size_t count)
{
	int rc;

	rc = kobject_synth_uevent(&mk->kobj, buffer, count);
	return rc ? rc : count;
}

struct module_attribute module_uevent =
	__ATTR(uevent, 0200, NULL, store_uevent);

static ssize_t show_coresize(struct module_attribute *mattr,
			     struct module_kobject *mk, char *buffer)
{
	return sprintf(buffer, "%u\n", mk->mod->core_layout.size);
}

static struct module_attribute modinfo_coresize =
	__ATTR(coresize, 0444, show_coresize, NULL);

static ssize_t show_initsize(struct module_attribute *mattr,
			     struct module_kobject *mk, char *buffer)
{
	return sprintf(buffer, "%u\n", mk->mod->init_layout.size);
}

static struct module_attribute modinfo_initsize =
	__ATTR(initsize, 0444, show_initsize, NULL);

static ssize_t show_taint(struct module_attribute *mattr,
			  struct module_kobject *mk, char *buffer)
{
	size_t l;

	l = module_flags_taint(mk->mod, buffer);
	buffer[l++] = '\n';
	return l;
}

static struct module_attribute modinfo_taint =
	__ATTR(taint, 0444, show_taint, NULL);

static struct module_attribute *modinfo_attrs[] = {
	&module_uevent,
	&modinfo_version,
	&modinfo_srcversion,
	&modinfo_initstate,
	&modinfo_coresize,
	&modinfo_initsize,
	&modinfo_taint,
	NULL,
};

static const char vermagic[] = VERMAGIC_STRING;

static int try_to_force_load(struct module *mod, const char *reason)
{
#ifdef CONFIG_MODULE_FORCE_LOAD
	if (!test_taint(TAINT_FORCED_MODULE))
		pr_warn("%s: %s: kernel tainted.\n", mod->name, reason);
	add_taint_module(mod, TAINT_FORCED_MODULE, LOCKDEP_NOW_UNRELIABLE);
	return 0;
#else
	return -ENOEXEC;
#endif
}

static char *get_modinfo(const struct load_info *info, const char *tag);
static char *get_next_modinfo(const struct load_info *info, const char *tag,
			      char *prev);

static int verify_namespace_is_imported(const struct load_info *info,
					const struct kernel_symbol *sym,
					struct module *mod)
{
	const char *namespace;
	char *imported_namespace;

	namespace = kernel_symbol_namespace(sym);
	if (namespace && namespace[0]) {
		imported_namespace = get_modinfo(info, "import_ns");
		while (imported_namespace) {
			if (strcmp(namespace, imported_namespace) == 0)
				return 0;
			imported_namespace = get_next_modinfo(
				info, "import_ns", imported_namespace);
		}
#ifdef CONFIG_MODULE_ALLOW_MISSING_NAMESPACE_IMPORTS
		pr_warn(
#else
		pr_err(
#endif
			"%s: module uses symbol (%s) from namespace %s, but does not import it.\n",
			mod->name, kernel_symbol_name(sym), namespace);
#ifndef CONFIG_MODULE_ALLOW_MISSING_NAMESPACE_IMPORTS
		return -EINVAL;
#endif
	}
	return 0;
}

static bool inherit_taint(struct module *mod, struct module *owner)
{
	if (!owner || !test_bit(TAINT_PROPRIETARY_MODULE, &owner->taints))
		return true;

	if (mod->using_gplonly_symbols) {
		pr_err("%s: module using GPL-only symbols uses symbols from proprietary module %s.\n",
			mod->name, owner->name);
		return false;
	}

	if (!test_bit(TAINT_PROPRIETARY_MODULE, &mod->taints)) {
		pr_warn("%s: module uses symbols from proprietary module %s, inheriting taint.\n",
			mod->name, owner->name);
		set_bit(TAINT_PROPRIETARY_MODULE, &mod->taints);
	}
	return true;
}

/* Resolve a symbol for this module.  I.e. if we find one, record usage. */
static const struct kernel_symbol *resolve_symbol(struct module *mod,
						  const struct load_info *info,
						  const char *name,
						  char ownername[])
{
	struct module *owner;
	const struct kernel_symbol *sym;
	const s32 *crc;
	enum mod_license license;
	int err;

	/*
	 * The module_mutex should not be a heavily contended lock;
	 * if we get the occasional sleep here, we'll go an extra iteration
	 * in the wait_event_interruptible(), which is harmless.
	 */
	sched_annotate_sleep();
	mutex_lock(&module_mutex);
	sym = find_symbol(name, &owner, &crc, &license,
			  !(mod->taints & (1 << TAINT_PROPRIETARY_MODULE)), true);
	if (!sym)
		goto unlock;

	if (license == GPL_ONLY)
		mod->using_gplonly_symbols = true;

	if (!inherit_taint(mod, owner)) {
		sym = NULL;
		goto getname;
	}

	err = verify_namespace_is_imported(info, sym, mod);
	if (err) {
		sym = ERR_PTR(err);
		goto getname;
	}

getname:
	/* We must make copy under the lock if we failed to get ref. */
	strncpy(ownername, module_name(owner), MODULE_NAME_LEN);
unlock:
	mutex_unlock(&module_mutex);
	return sym;
}

static const struct kernel_symbol *
resolve_symbol_wait(struct module *mod,
		    const struct load_info *info,
		    const char *name)
{
	const struct kernel_symbol *ksym;
	char owner[MODULE_NAME_LEN];

	if (wait_event_interruptible_timeout(module_wq,
			!IS_ERR(ksym = resolve_symbol(mod, info, name, owner))
			|| PTR_ERR(ksym) != -EBUSY,
					     30 * HZ) <= 0) {
		pr_warn("%s: gave up waiting for init of module %s.\n",
			mod->name, owner);
	}
	return ksym;
}

/*
 * /sys/module/foo/sections stuff
 * J. Corbet <corbet@lwn.net>
 */
#ifdef CONFIG_SYSFS

#ifdef CONFIG_KALLSYMS
static inline bool sect_empty(const Elf_Shdr *sect)
{
	return !(sect->sh_flags & SHF_ALLOC) || sect->sh_size == 0;
}

struct module_sect_attr {
	struct bin_attribute battr;
	unsigned long address;
};

struct module_sect_attrs {
	struct attribute_group grp;
	unsigned int nsections;
	struct module_sect_attr attrs[];
};

#define MODULE_SECT_READ_SIZE (3 /* "0x", "\n" */ + (BITS_PER_LONG / 4))
static ssize_t module_sect_read(struct file *file, struct kobject *kobj,
				struct bin_attribute *battr,
				char *buf, loff_t pos, size_t count)
{
	struct module_sect_attr *sattr =
		container_of(battr, struct module_sect_attr, battr);
	char bounce[MODULE_SECT_READ_SIZE + 1];
	size_t wrote;

	if (pos != 0)
		return -EINVAL;

	/*
	 * Since we're a binary read handler, we must account for the
	 * trailing NUL byte that sprintf will write: if "buf" is
	 * too small to hold the NUL, or the NUL is exactly the last
	 * byte, the read will look like it got truncated by one byte.
	 * Since there is no way to ask sprintf nicely to not write
	 * the NUL, we have to use a bounce buffer.
	 */
	wrote = scnprintf(bounce, sizeof(bounce), "0x%px\n",
			 kallsyms_show_value(file->f_cred)
				? (void *)sattr->address : NULL);
	count = min(count, wrote);
	memcpy(buf, bounce, count);

	return count;
}

static void free_sect_attrs(struct module_sect_attrs *sect_attrs)
{
	unsigned int section;

	for (section = 0; section < sect_attrs->nsections; section++)
		kfree(sect_attrs->attrs[section].battr.attr.name);
	kfree(sect_attrs);
}

static void add_sect_attrs(struct module *mod, const struct load_info *info)
{
	unsigned int nloaded = 0, i, size[2];
	struct module_sect_attrs *sect_attrs;
	struct module_sect_attr *sattr;
	struct bin_attribute **gattr;

	/* Count loaded sections and allocate structures */
	for (i = 0; i < info->hdr->e_shnum; i++)
		if (!sect_empty(&info->sechdrs[i]))
			nloaded++;
	size[0] = ALIGN(struct_size(sect_attrs, attrs, nloaded),
			sizeof(sect_attrs->grp.bin_attrs[0]));
	size[1] = (nloaded + 1) * sizeof(sect_attrs->grp.bin_attrs[0]);
	sect_attrs = kzalloc(size[0] + size[1], GFP_KERNEL);
	if (sect_attrs == NULL)
		return;

	/* Setup section attributes. */
	sect_attrs->grp.name = "sections";
	sect_attrs->grp.bin_attrs = (void *)sect_attrs + size[0];

	sect_attrs->nsections = 0;
	sattr = &sect_attrs->attrs[0];
	gattr = &sect_attrs->grp.bin_attrs[0];
	for (i = 0; i < info->hdr->e_shnum; i++) {
		Elf_Shdr *sec = &info->sechdrs[i];
		if (sect_empty(sec))
			continue;
		sysfs_bin_attr_init(&sattr->battr);
		sattr->address = sec->sh_addr;
		sattr->battr.attr.name =
			kstrdup(info->secstrings + sec->sh_name, GFP_KERNEL);
		if (sattr->battr.attr.name == NULL)
			goto out;
		sect_attrs->nsections++;
		sattr->battr.read = module_sect_read;
		sattr->battr.size = MODULE_SECT_READ_SIZE;
		sattr->battr.attr.mode = 0400;
		*(gattr++) = &(sattr++)->battr;
	}
	*gattr = NULL;

	if (sysfs_create_group(&mod->mkobj.kobj, &sect_attrs->grp))
		goto out;

	mod->sect_attrs = sect_attrs;
	return;
  out:
	free_sect_attrs(sect_attrs);
}

static void remove_sect_attrs(struct module *mod)
{
	if (mod->sect_attrs) {
		sysfs_remove_group(&mod->mkobj.kobj,
				   &mod->sect_attrs->grp);
		/* We are positive that no one is using any sect attrs
		 * at this point.  Deallocate immediately. */
		free_sect_attrs(mod->sect_attrs);
		mod->sect_attrs = NULL;
	}
}

/*
 * /sys/module/foo/notes/.section.name gives contents of SHT_NOTE sections.
 */

struct module_notes_attrs {
	struct kobject *dir;
	unsigned int notes;
	struct bin_attribute attrs[];
};

static ssize_t module_notes_read(struct file *filp, struct kobject *kobj,
				 struct bin_attribute *bin_attr,
				 char *buf, loff_t pos, size_t count)
{
	/*
	 * The caller checked the pos and count against our size.
	 */
	memcpy(buf, bin_attr->private + pos, count);
	return count;
}

static void free_notes_attrs(struct module_notes_attrs *notes_attrs,
			     unsigned int i)
{
	if (notes_attrs->dir) {
		while (i-- > 0)
			sysfs_remove_bin_file(notes_attrs->dir,
					      &notes_attrs->attrs[i]);
		kobject_put(notes_attrs->dir);
	}
	kfree(notes_attrs);
}

static void add_notes_attrs(struct module *mod, const struct load_info *info)
{
	unsigned int notes, loaded, i;
	struct module_notes_attrs *notes_attrs;
	struct bin_attribute *nattr;

	/* failed to create section attributes, so can't create notes */
	if (!mod->sect_attrs)
		return;

	/* Count notes sections and allocate structures.  */
	notes = 0;
	for (i = 0; i < info->hdr->e_shnum; i++)
		if (!sect_empty(&info->sechdrs[i]) &&
		    (info->sechdrs[i].sh_type == SHT_NOTE))
			++notes;

	if (notes == 0)
		return;

	notes_attrs = kzalloc(struct_size(notes_attrs, attrs, notes),
			      GFP_KERNEL);
	if (notes_attrs == NULL)
		return;

	notes_attrs->notes = notes;
	nattr = &notes_attrs->attrs[0];
	for (loaded = i = 0; i < info->hdr->e_shnum; ++i) {
		if (sect_empty(&info->sechdrs[i]))
			continue;
		if (info->sechdrs[i].sh_type == SHT_NOTE) {
			sysfs_bin_attr_init(nattr);
			nattr->attr.name = mod->sect_attrs->attrs[loaded].battr.attr.name;
			nattr->attr.mode = S_IRUGO;
			nattr->size = info->sechdrs[i].sh_size;
			nattr->private = (void *) info->sechdrs[i].sh_addr;
			nattr->read = module_notes_read;
			++nattr;
		}
		++loaded;
	}

	notes_attrs->dir = kobject_create_and_add("notes", &mod->mkobj.kobj);
	if (!notes_attrs->dir)
		goto out;

	for (i = 0; i < notes; ++i)
		if (sysfs_create_bin_file(notes_attrs->dir,
					  &notes_attrs->attrs[i]))
			goto out;

	mod->notes_attrs = notes_attrs;
	return;

  out:
	free_notes_attrs(notes_attrs, i);
}

static void remove_notes_attrs(struct module *mod)
{
	if (mod->notes_attrs)
		free_notes_attrs(mod->notes_attrs, mod->notes_attrs->notes);
}

#else

static inline void add_sect_attrs(struct module *mod,
				  const struct load_info *info)
{
}

static inline void remove_sect_attrs(struct module *mod)
{
}

static inline void add_notes_attrs(struct module *mod,
				   const struct load_info *info)
{
}

static inline void remove_notes_attrs(struct module *mod)
{
}
#endif /* CONFIG_KALLSYMS */

static void module_remove_modinfo_attrs(struct module *mod, int end);

static int module_add_modinfo_attrs(struct module *mod)
{
	struct module_attribute *attr;
	struct module_attribute *temp_attr;
	int error = 0;
	int i;

	mod->modinfo_attrs = kzalloc((sizeof(struct module_attribute) *
					(ARRAY_SIZE(modinfo_attrs) + 1)),
					GFP_KERNEL);
	if (!mod->modinfo_attrs)
		return -ENOMEM;

	temp_attr = mod->modinfo_attrs;
	for (i = 0; (attr = modinfo_attrs[i]); i++) {
		if (!attr->test || attr->test(mod)) {
			memcpy(temp_attr, attr, sizeof(*temp_attr));
			sysfs_attr_init(&temp_attr->attr);
			error = sysfs_create_file(&mod->mkobj.kobj,
					&temp_attr->attr);
			if (error)
				goto error_out;
			++temp_attr;
		}
	}

	return 0;

error_out:
	if (i > 0)
		module_remove_modinfo_attrs(mod, --i);
	else
		kfree(mod->modinfo_attrs);
	return error;
}

static void module_remove_modinfo_attrs(struct module *mod, int end)
{
	struct module_attribute *attr;
	int i;

	for (i = 0; (attr = &mod->modinfo_attrs[i]); i++) {
		if (end >= 0 && i > end)
			break;
		/* pick a field to test for end of list */
		if (!attr->attr.name)
			break;
		sysfs_remove_file(&mod->mkobj.kobj, &attr->attr);
		if (attr->free)
			attr->free(mod);
	}
	kfree(mod->modinfo_attrs);
}

static void mod_kobject_put(struct module *mod)
{
	DECLARE_COMPLETION_ONSTACK(c);
	mod->mkobj.kobj_completion = &c;
	kobject_put(&mod->mkobj.kobj);
	wait_for_completion(&c);
}

static int mod_sysfs_init(struct module *mod)
{
	int err;
	struct kobject *kobj;

	if (!module_sysfs_initialized) {
		pr_err("%s: module sysfs not initialized\n", mod->name);
		err = -EINVAL;
		goto out;
	}

	kobj = kset_find_obj(module_kset, mod->name);
	if (kobj) {
		pr_err("%s: module is already loaded\n", mod->name);
		kobject_put(kobj);
		err = -EINVAL;
		goto out;
	}

	mod->mkobj.mod = mod;

	memset(&mod->mkobj.kobj, 0, sizeof(mod->mkobj.kobj));
	mod->mkobj.kobj.kset = module_kset;
	err = kobject_init_and_add(&mod->mkobj.kobj, &module_ktype, NULL,
				   "%s", mod->name);
	if (err)
		mod_kobject_put(mod);

out:
	return err;
}

static int mod_sysfs_setup(struct module *mod,
			   const struct load_info *info,
			   struct kernel_param *kparam,
			   unsigned int num_params)
{
	int err;

	err = mod_sysfs_init(mod);
	if (err)
		goto out;

	mod->holders_dir = kobject_create_and_add("holders", &mod->mkobj.kobj);
	if (!mod->holders_dir) {
		err = -ENOMEM;
		goto out_unreg;
	}

	err = module_param_sysfs_setup(mod, kparam, num_params);
	if (err)
		goto out_unreg_holders;

	err = module_add_modinfo_attrs(mod);
	if (err)
		goto out_unreg_param;

	add_sect_attrs(mod, info);
	add_notes_attrs(mod, info);

	return 0;

out_unreg_modinfo_attrs:
	module_remove_modinfo_attrs(mod, -1);
out_unreg_param:
	module_param_sysfs_remove(mod);
out_unreg_holders:
	kobject_put(mod->holders_dir);
out_unreg:
	mod_kobject_put(mod);
out:
	return err;
}

static void mod_sysfs_fini(struct module *mod)
{
	remove_notes_attrs(mod);
	remove_sect_attrs(mod);
	mod_kobject_put(mod);
}

static void init_param_lock(struct module *mod)
{
	mutex_init(&mod->param_lock);
}
#else /* !CONFIG_SYSFS */

static int mod_sysfs_setup(struct module *mod,
			   const struct load_info *info,
			   struct kernel_param *kparam,
			   unsigned int num_params)
{
	return 0;
}

static void mod_sysfs_fini(struct module *mod)
{
}

static void module_remove_modinfo_attrs(struct module *mod, int end)
{
}

static void init_param_lock(struct module *mod)
{
}
#endif /* CONFIG_SYSFS */

static void mod_sysfs_teardown(struct module *mod)
{
	module_remove_modinfo_attrs(mod, -1);
	module_param_sysfs_remove(mod);
	kobject_put(mod->mkobj.drivers_dir);
	kobject_put(mod->holders_dir);
	mod_sysfs_fini(mod);
}

/*
 * LKM RO/NX protection: protect module's text/ro-data
 * from modification and any data from execution.
 *
 * General layout of module is:
 *          [text] [read-only-data] [ro-after-init] [writable data]
 * text_size -----^                ^               ^               ^
 * ro_size ------------------------|               |               |
 * ro_after_init_size -----------------------------|               |
 * size -----------------------------------------------------------|
 *
 * These values are always page-aligned (as is base)
 */

/*
 * Since some arches are moving towards PAGE_KERNEL module allocations instead
 * of PAGE_KERNEL_EXEC, keep frob_text() and module_enable_x() outside of the
 * CONFIG_STRICT_MODULE_RWX block below because they are needed regardless of
 * whether we are strict.
 */
#ifdef CONFIG_ARCH_HAS_STRICT_MODULE_RWX
static void frob_text(const struct module_layout *layout,
		      int (*set_memory)(unsigned long start, int num_pages))
{
	BUG_ON((unsigned long)layout->base & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->text_size & (PAGE_SIZE-1));
	set_memory((unsigned long)layout->base,
		   layout->text_size >> PAGE_SHIFT);
}

static void module_enable_x(const struct module *mod)
{
	frob_text(&mod->core_layout, set_memory_x);
	frob_text(&mod->init_layout, set_memory_x);
}
#else /* !CONFIG_ARCH_HAS_STRICT_MODULE_RWX */
static void module_enable_x(const struct module *mod) { }
#endif /* CONFIG_ARCH_HAS_STRICT_MODULE_RWX */

#ifdef CONFIG_STRICT_MODULE_RWX
static void frob_rodata(const struct module_layout *layout,
			int (*set_memory)(unsigned long start, int num_pages))
{
	BUG_ON((unsigned long)layout->base & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->text_size & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->ro_size & (PAGE_SIZE-1));
	set_memory((unsigned long)layout->base + layout->text_size,
		   (layout->ro_size - layout->text_size) >> PAGE_SHIFT);
}

static void frob_ro_after_init(const struct module_layout *layout,
				int (*set_memory)(unsigned long start, int num_pages))
{
	BUG_ON((unsigned long)layout->base & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->ro_size & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->ro_after_init_size & (PAGE_SIZE-1));
	set_memory((unsigned long)layout->base + layout->ro_size,
		   (layout->ro_after_init_size - layout->ro_size) >> PAGE_SHIFT);
}

static void frob_writable_data(const struct module_layout *layout,
			       int (*set_memory)(unsigned long start, int num_pages))
{
	BUG_ON((unsigned long)layout->base & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->ro_after_init_size & (PAGE_SIZE-1));
	BUG_ON((unsigned long)layout->size & (PAGE_SIZE-1));
	set_memory((unsigned long)layout->base + layout->ro_after_init_size,
		   (layout->size - layout->ro_after_init_size) >> PAGE_SHIFT);
}

static void module_enable_ro(const struct module *mod, bool after_init)
{
	if (!rodata_enabled)
		return;

	set_vm_flush_reset_perms(mod->core_layout.base);
	set_vm_flush_reset_perms(mod->init_layout.base);
	frob_text(&mod->core_layout, set_memory_ro);

	frob_rodata(&mod->core_layout, set_memory_ro);
	frob_text(&mod->init_layout, set_memory_ro);
	frob_rodata(&mod->init_layout, set_memory_ro);

	if (after_init)
		frob_ro_after_init(&mod->core_layout, set_memory_ro);
}

static void module_enable_nx(const struct module *mod)
{
	frob_rodata(&mod->core_layout, set_memory_nx);
	frob_ro_after_init(&mod->core_layout, set_memory_nx);
	frob_writable_data(&mod->core_layout, set_memory_nx);
	frob_rodata(&mod->init_layout, set_memory_nx);
	frob_writable_data(&mod->init_layout, set_memory_nx);
}

static int module_enforce_rwx_sections(Elf_Ehdr *hdr, Elf_Shdr *sechdrs,
				       char *secstrings, struct module *mod)
{
	const unsigned long shf_wx = SHF_WRITE|SHF_EXECINSTR;
	int i;

	for (i = 0; i < hdr->e_shnum; i++) {
		if ((sechdrs[i].sh_flags & shf_wx) == shf_wx) {
			pr_err("%s: section %s (index %d) has invalid WRITE|EXEC flags\n",
				mod->name, secstrings + sechdrs[i].sh_name, i);
			return -ENOEXEC;
		}
	}

	return 0;
}

#else /* !CONFIG_STRICT_MODULE_RWX */
static void module_enable_nx(const struct module *mod) { }
static void module_enable_ro(const struct module *mod, bool after_init) {}
static int module_enforce_rwx_sections(Elf_Ehdr *hdr, Elf_Shdr *sechdrs,
				       char *secstrings, struct module *mod)
{
	return 0;
}
#endif /*  CONFIG_STRICT_MODULE_RWX */

void __weak module_memfree(void *module_region)
{
	/*
	 * This memory may be RO, and freeing RO memory in an interrupt is not
	 * supported by vmalloc.
	 */
	WARN_ON(in_interrupt());
	vfree(module_region);
}

void __weak module_arch_cleanup(struct module *mod)
{
}

void __weak module_arch_freeing_init(struct module *mod)
{
}

/* Free a module, remove from lists, etc. */
static void free_module(struct module *mod)
{
	trace_module_free(mod);

	mod_sysfs_teardown(mod);

	/* We leave it in list to prevent duplicate loads, but make sure
	 * that noone uses it while it's being deconstructed. */
	mutex_lock(&module_mutex);
	mod->state = MODULE_STATE_UNFORMED;
	mutex_unlock(&module_mutex);

	/* Remove dynamic debug info */
	ddebug_remove_module(mod->name);

	/* Arch-specific cleanup. */
	module_arch_cleanup(mod);

	/* Free any allocated parameters. */
	destroy_params(mod->kp, mod->num_kp);

//	if (is_livepatch_module(mod))
//		free_module_elf(mod);

	/* Now we can delete it from the lists */
	mutex_lock(&module_mutex);
	/* Unlink carefully: kallsyms could be walking list. */
	list_del_rcu(&mod->list);
	mod_tree_remove(mod);
	/* Remove this module from bug list, this uses list_del_rcu */
	module_bug_cleanup(mod);
	/* Wait for RCU-sched synchronizing before releasing mod->list and buglist. */
	synchronize_rcu();
	mutex_unlock(&module_mutex);

	/* This may be empty, but that's OK */
	module_arch_freeing_init(mod);
	module_memfree(mod->init_layout.base);
	percpu_modfree(mod);

	/* Free lock-classes; relies on the preceding sync_rcu(). */
	lockdep_free_key_range(mod->core_layout.base, mod->core_layout.size);

	/* Finally, free the core (containing the module structure) */
	module_memfree(mod->core_layout.base);
}

/*
 * Ensure that an exported symbol [global namespace] does not already exist
 * in the kernel or in some other module's exported symbol table.
 *
 * You must hold the module_mutex.
 */
static int verify_exported_symbols(struct module *mod)
{
	unsigned int i;
	struct module *owner;
	const struct kernel_symbol *s;
	struct {
		const struct kernel_symbol *sym;
		unsigned int num;
	} arr[] = {
		{ mod->syms, mod->num_syms },
		{ mod->gpl_syms, mod->num_gpl_syms },
		{ mod->gpl_future_syms, mod->num_gpl_future_syms },
#ifdef CONFIG_UNUSED_SYMBOLS
		{ mod->unused_syms, mod->num_unused_syms },
		{ mod->unused_gpl_syms, mod->num_unused_gpl_syms },
#endif
	};

	for (i = 0; i < ARRAY_SIZE(arr); i++) {
		for (s = arr[i].sym; s < arr[i].sym + arr[i].num; s++) {
			if (find_symbol(kernel_symbol_name(s), &owner, NULL,
					NULL, true, false)) {
				pr_err("%s: exports duplicate symbol %s"
				       " (owned by %s)\n",
				       mod->name, kernel_symbol_name(s),
				       module_name(owner));
				return -ENOEXEC;
			}
		}
	}
	return 0;
}

/* Change all symbols so that st_value encodes the pointer directly. */
static int simplify_symbols(struct module *mod, const struct load_info *info)
{
	Elf_Shdr *symsec = &info->sechdrs[info->index.sym];
	Elf_Sym *sym = (void *)symsec->sh_addr;
	unsigned long secbase;
	unsigned int i;
	int ret = 0;
	const struct kernel_symbol *ksym;

	for (i = 1; i < symsec->sh_size / sizeof(Elf_Sym); i++) {
		const char *name = info->strtab + sym[i].st_name;

		switch (sym[i].st_shndx) {
		case SHN_COMMON:
			/* Ignore common symbols */
			if (!strncmp(name, "__gnu_lto", 9))
				break;

			/* We compiled with -fno-common.  These are not
			   supposed to happen.  */
			pr_debug("Common symbol: %s\n", name);
			pr_warn("%s: please compile with -fno-common\n",
			       mod->name);
			ret = -ENOEXEC;
			break;

		case SHN_ABS:
			/* Don't need to do anything */
			pr_debug("Absolute symbol: 0x%08lx\n",
			       (long)sym[i].st_value);
			break;

		case SHN_LIVEPATCH:
			/* Livepatch symbols are resolved by livepatch */
			break;

		case SHN_UNDEF:
			ksym = resolve_symbol_wait(mod, info, name);
			/* Ok if resolved.  */
			if (ksym && !IS_ERR(ksym)) {
				sym[i].st_value = kernel_symbol_value(ksym);
				break;
			}

			/* Ok if weak.  */
			if (!ksym && ELF_ST_BIND(sym[i].st_info) == STB_WEAK)
				break;

			ret = PTR_ERR(ksym) ?: -ENOENT;
			pr_warn("%s: Unknown symbol %s (err %d)\n",
				mod->name, name, ret);
			break;

		default:
			/* Divert to percpu allocation if a percpu var. */
			if (sym[i].st_shndx == info->index.pcpu)
				secbase = (unsigned long)mod_percpu(mod);
			else
				secbase = info->sechdrs[sym[i].st_shndx].sh_addr;
			sym[i].st_value += secbase;
			break;
		}
	}

	return ret;
}

static int apply_relocations(struct module *mod, const struct load_info *info)
{
	unsigned int i;
	int err = 0;

	/* Now do relocations. */
	for (i = 1; i < info->hdr->e_shnum; i++) {
		unsigned int infosec = info->sechdrs[i].sh_info;

		/* Not a valid relocation section? */
		if (infosec >= info->hdr->e_shnum)
			continue;

		/* Don't bother with non-allocated sections */
		if (!(info->sechdrs[infosec].sh_flags & SHF_ALLOC))
			continue;

		if (info->sechdrs[i].sh_flags & SHF_RELA_LIVEPATCH)
			err = klp_apply_section_relocs(mod, info->sechdrs,
						       info->secstrings,
						       info->strtab,
						       info->index.sym, i,
						       NULL);
		else if (info->sechdrs[i].sh_type == SHT_REL)
			err = apply_relocate(info->sechdrs, info->strtab,
					     info->index.sym, i, mod);
		else if (info->sechdrs[i].sh_type == SHT_RELA)
			err = apply_relocate_add(info->sechdrs, info->strtab,
						 info->index.sym, i, mod);
		if (err < 0)
			break;
	}
	return err;
}

/* Additional bytes needed by arch in front of individual sections */
unsigned int __weak arch_mod_section_prepend(struct module *mod,
					     unsigned int section)
{
	/* default implementation just returns zero */
	return 0;
}

/* Update size with this section: return offset. */
static long get_offset(struct module *mod, unsigned int *size,
		       Elf_Shdr *sechdr, unsigned int section)
{
	long ret;

	*size += arch_mod_section_prepend(mod, section);
	ret = ALIGN(*size, sechdr->sh_addralign ?: 1);
	*size = ret + sechdr->sh_size;
	return ret;
}

/* Lay out the SHF_ALLOC sections in a way not dissimilar to how ld
   might -- code, read-only data, read-write data, small data.  Tally
   sizes, and place the offsets into sh_entsize fields: high bit means it
   belongs in init. */
static void layout_sections(struct module *mod, struct load_info *info)
{
	static unsigned long const masks[][2] = {
		/* NOTE: all executable code must be the first section
		 * in this array; otherwise modify the text_size
		 * finder in the two loops below */
		{ SHF_EXECINSTR | SHF_ALLOC, ARCH_SHF_SMALL },
		{ SHF_ALLOC, SHF_WRITE | ARCH_SHF_SMALL },
		{ SHF_RO_AFTER_INIT | SHF_ALLOC, ARCH_SHF_SMALL },
		{ SHF_WRITE | SHF_ALLOC, ARCH_SHF_SMALL },
		{ ARCH_SHF_SMALL | SHF_ALLOC, 0 }
	};
	unsigned int m, i;

	for (i = 0; i < info->hdr->e_shnum; i++)
		info->sechdrs[i].sh_entsize = ~0UL;

	pr_debug("Core section allocation order:\n");
	for (m = 0; m < ARRAY_SIZE(masks); ++m) {
		for (i = 0; i < info->hdr->e_shnum; ++i) {
			Elf_Shdr *s = &info->sechdrs[i];
			const char *sname = info->secstrings + s->sh_name;

			if ((s->sh_flags & masks[m][0]) != masks[m][0]
			    || (s->sh_flags & masks[m][1])
			    || s->sh_entsize != ~0UL
			    || module_init_section(sname))
				continue;
			s->sh_entsize = get_offset(mod, &mod->core_layout.size, s, i);
			pr_debug("\t%s\n", sname);
		}
		switch (m) {
		case 0: /* executable */
			mod->core_layout.size = debug_align(mod->core_layout.size);
			mod->core_layout.text_size = mod->core_layout.size;
			break;
		case 1: /* RO: text and ro-data */
			mod->core_layout.size = debug_align(mod->core_layout.size);
			mod->core_layout.ro_size = mod->core_layout.size;
			break;
		case 2: /* RO after init */
			mod->core_layout.size = debug_align(mod->core_layout.size);
			mod->core_layout.ro_after_init_size = mod->core_layout.size;
			break;
		case 4: /* whole core */
			mod->core_layout.size = debug_align(mod->core_layout.size);
			break;
		}
	}

	pr_debug("Init section allocation order:\n");
	for (m = 0; m < ARRAY_SIZE(masks); ++m) {
		for (i = 0; i < info->hdr->e_shnum; ++i) {
			Elf_Shdr *s = &info->sechdrs[i];
			const char *sname = info->secstrings + s->sh_name;

			if ((s->sh_flags & masks[m][0]) != masks[m][0]
			    || (s->sh_flags & masks[m][1])
			    || s->sh_entsize != ~0UL
			    || !module_init_section(sname))
				continue;
			s->sh_entsize = (get_offset(mod, &mod->init_layout.size, s, i)
					 | INIT_OFFSET_MASK);
			pr_debug("\t%s\n", sname);
		}
		switch (m) {
		case 0: /* executable */
			mod->init_layout.size = debug_align(mod->init_layout.size);
			mod->init_layout.text_size = mod->init_layout.size;
			break;
		case 1: /* RO: text and ro-data */
			mod->init_layout.size = debug_align(mod->init_layout.size);
			mod->init_layout.ro_size = mod->init_layout.size;
			break;
		case 2:
			/*
			 * RO after init doesn't apply to init_layout (only
			 * core_layout), so it just takes the value of ro_size.
			 */
			mod->init_layout.ro_after_init_size = mod->init_layout.ro_size;
			break;
		case 4: /* whole init */
			mod->init_layout.size = debug_align(mod->init_layout.size);
			break;
		}
	}
}

/* Parse tag=value strings from .modinfo section */
static char *next_string(char *string, unsigned long *secsize)
{
	/* Skip non-zero chars */
	while (string[0]) {
		string++;
		if ((*secsize)-- <= 1)
			return NULL;
	}

	/* Skip any zero padding. */
	while (!string[0]) {
		string++;
		if ((*secsize)-- <= 1)
			return NULL;
	}
	return string;
}

static char *get_next_modinfo(const struct load_info *info, const char *tag,
			      char *prev)
{
	char *p;
	unsigned int taglen = strlen(tag);
	Elf_Shdr *infosec = &info->sechdrs[info->index.info];
	unsigned long size = infosec->sh_size;

	/*
	 * get_modinfo() calls made before rewrite_section_headers()
	 * must use sh_offset, as sh_addr isn't set!
	 */
	char *modinfo = (char *)info->hdr + infosec->sh_offset;

	if (prev) {
		size -= prev - modinfo;
		modinfo = next_string(prev, &size);
	}

	for (p = modinfo; p; p = next_string(p, &size)) {
		if (strncmp(p, tag, taglen) == 0 && p[taglen] == '=')
			return p + taglen + 1;
	}
	return NULL;
}

static char *get_modinfo(const struct load_info *info, const char *tag)
{
	return get_next_modinfo(info, tag, NULL);
}

static void setup_modinfo(struct module *mod, struct load_info *info)
{
	struct module_attribute *attr;
	int i;

	for (i = 0; (attr = modinfo_attrs[i]); i++) {
		if (attr->setup)
			attr->setup(mod, get_modinfo(info, attr->attr.name));
	}
}

static void free_modinfo(struct module *mod)
{
	struct module_attribute *attr;
	int i;

	for (i = 0; (attr = modinfo_attrs[i]); i++) {
		if (attr->free)
			attr->free(mod);
	}
}

#ifdef CONFIG_KALLSYMS

/* As per nm */
static char elf_type(const Elf_Sym *sym, const struct load_info *info)
{
	const Elf_Shdr *sechdrs = info->sechdrs;

	if (ELF_ST_BIND(sym->st_info) == STB_WEAK) {
		if (ELF_ST_TYPE(sym->st_info) == STT_OBJECT)
			return 'v';
		else
			return 'w';
	}
	if (sym->st_shndx == SHN_UNDEF)
		return 'U';
	if (sym->st_shndx == SHN_ABS || sym->st_shndx == info->index.pcpu)
		return 'a';
	if (sym->st_shndx >= SHN_LORESERVE)
		return '?';
	if (sechdrs[sym->st_shndx].sh_flags & SHF_EXECINSTR)
		return 't';
	if (sechdrs[sym->st_shndx].sh_flags & SHF_ALLOC
	    && sechdrs[sym->st_shndx].sh_type != SHT_NOBITS) {
		if (!(sechdrs[sym->st_shndx].sh_flags & SHF_WRITE))
			return 'r';
		else if (sechdrs[sym->st_shndx].sh_flags & ARCH_SHF_SMALL)
			return 'g';
		else
			return 'd';
	}
	if (sechdrs[sym->st_shndx].sh_type == SHT_NOBITS) {
		if (sechdrs[sym->st_shndx].sh_flags & ARCH_SHF_SMALL)
			return 's';
		else
			return 'b';
	}
	if (strstarts(info->secstrings + sechdrs[sym->st_shndx].sh_name,
		      ".debug")) {
		return 'n';
	}
	return '?';
}

static bool is_core_symbol(const Elf_Sym *src, const Elf_Shdr *sechdrs,
			unsigned int shnum, unsigned int pcpundx)
{
	const Elf_Shdr *sec;

	if (src->st_shndx == SHN_UNDEF
	    || src->st_shndx >= shnum
	    || !src->st_name)
		return false;

#ifdef CONFIG_KALLSYMS_ALL
	if (src->st_shndx == pcpundx)
		return true;
#endif

	sec = sechdrs + src->st_shndx;
	if (!(sec->sh_flags & SHF_ALLOC)
#ifndef CONFIG_KALLSYMS_ALL
	    || !(sec->sh_flags & SHF_EXECINSTR)
#endif
	    || (sec->sh_entsize & INIT_OFFSET_MASK))
		return false;

	return true;
}

/*
 * We only allocate and copy the strings needed by the parts of symtab
 * we keep.  This is simple, but has the effect of making multiple
 * copies of duplicates.  We could be more sophisticated, see
 * linux-kernel thread starting with
 * <73defb5e4bca04a6431392cc341112b1@localhost>.
 */
static void layout_symtab(struct module *mod, struct load_info *info)
{
	Elf_Shdr *symsect = info->sechdrs + info->index.sym;
	Elf_Shdr *strsect = info->sechdrs + info->index.str;
	const Elf_Sym *src;
	unsigned int i, nsrc, ndst, strtab_size = 0;

	/* Put symbol section at end of init part of module. */
	symsect->sh_flags |= SHF_ALLOC;
	symsect->sh_entsize = get_offset(mod, &mod->init_layout.size, symsect,
					 info->index.sym) | INIT_OFFSET_MASK;
	pr_debug("\t%s\n", info->secstrings + symsect->sh_name);

	src = (void *)info->hdr + symsect->sh_offset;
	nsrc = symsect->sh_size / sizeof(*src);

	/* Compute total space required for the core symbols' strtab. */
	for (ndst = i = 0; i < nsrc; i++) {
		if (i == 0 || is_livepatch_module(mod) ||
		    is_core_symbol(src+i, info->sechdrs, info->hdr->e_shnum,
				   info->index.pcpu)) {
			strtab_size += strlen(&info->strtab[src[i].st_name])+1;
			ndst++;
		}
	}

	/* Append room for core symbols at end of core part. */
	info->symoffs = ALIGN(mod->core_layout.size, symsect->sh_addralign ?: 1);
	info->stroffs = mod->core_layout.size = info->symoffs + ndst * sizeof(Elf_Sym);
	mod->core_layout.size += strtab_size;
	info->core_typeoffs = mod->core_layout.size;
	mod->core_layout.size += ndst * sizeof(char);
	mod->core_layout.size = debug_align(mod->core_layout.size);

	/* Put string table section at end of init part of module. */
	strsect->sh_flags |= SHF_ALLOC;
	strsect->sh_entsize = get_offset(mod, &mod->init_layout.size, strsect,
					 info->index.str) | INIT_OFFSET_MASK;
	pr_debug("\t%s\n", info->secstrings + strsect->sh_name);

	/* We'll tack temporary mod_kallsyms on the end. */
	mod->init_layout.size = ALIGN(mod->init_layout.size,
				      __alignof__(struct mod_kallsyms));
	info->mod_kallsyms_init_off = mod->init_layout.size;
	mod->init_layout.size += sizeof(struct mod_kallsyms);
	info->init_typeoffs = mod->init_layout.size;
	mod->init_layout.size += nsrc * sizeof(char);
	mod->init_layout.size = debug_align(mod->init_layout.size);
}

/*
 * We use the full symtab and strtab which layout_symtab arranged to
 * be appended to the init section.  Later we switch to the cut-down
 * core-only ones.
 */
static void add_kallsyms(struct module *mod, const struct load_info *info)
{
	unsigned int i, ndst;
	const Elf_Sym *src;
	Elf_Sym *dst;
	char *s;
	Elf_Shdr *symsec = &info->sechdrs[info->index.sym];

	/* Set up to point into init section. */
	mod->kallsyms = mod->init_layout.base + info->mod_kallsyms_init_off;

	mod->kallsyms->symtab = (void *)symsec->sh_addr;
	mod->kallsyms->num_symtab = symsec->sh_size / sizeof(Elf_Sym);
	/* Make sure we get permanent strtab: don't use info->strtab. */
	mod->kallsyms->strtab = (void *)info->sechdrs[info->index.str].sh_addr;
	mod->kallsyms->typetab = mod->init_layout.base + info->init_typeoffs;

	/*
	 * Now populate the cut down core kallsyms for after init
	 * and set types up while we still have access to sections.
	 */
	mod->core_kallsyms.symtab = dst = mod->core_layout.base + info->symoffs;
	mod->core_kallsyms.strtab = s = mod->core_layout.base + info->stroffs;
	mod->core_kallsyms.typetab = mod->core_layout.base + info->core_typeoffs;
	src = mod->kallsyms->symtab;
	for (ndst = i = 0; i < mod->kallsyms->num_symtab; i++) {
		mod->kallsyms->typetab[i] = elf_type(src + i, info);
		if (i == 0 || is_livepatch_module(mod) ||
		    is_core_symbol(src+i, info->sechdrs, info->hdr->e_shnum,
				   info->index.pcpu)) {
			mod->core_kallsyms.typetab[ndst] =
			    mod->kallsyms->typetab[i];
			dst[ndst] = src[i];
			dst[ndst++].st_name = s - mod->core_kallsyms.strtab;
			s += strlcpy(s, &mod->kallsyms->strtab[src[i].st_name],
				     KSYM_NAME_LEN) + 1;
		}
	}
	mod->core_kallsyms.num_symtab = ndst;
}
#else
static inline void layout_symtab(struct module *mod, struct load_info *info)
{
}

static void add_kallsyms(struct module *mod, const struct load_info *info)
{
}
#endif /* CONFIG_KALLSYMS */

static void dynamic_debug_setup(struct module *mod, struct _ddebug *debug, unsigned int num)
{
	if (!debug)
		return;
	ddebug_add_module(debug, num, mod->name);
}

static void dynamic_debug_remove(struct module *mod, struct _ddebug *debug)
{
	if (debug)
		ddebug_remove_module(mod->name);
}

void * __weak module_alloc(unsigned long size)
{
	return __vmalloc_node_range(size, 1, VMALLOC_START, VMALLOC_END,
			GFP_KERNEL, PAGE_KERNEL_EXEC, VM_FLUSH_RESET_PERMS,
			NUMA_NO_NODE, __builtin_return_address(0));
}

bool __weak module_init_section(const char *name)
{
	return strstarts(name, ".init");
}

bool __weak module_exit_section(const char *name)
{
	return strstarts(name, ".exit");
}

/* Sanity checks against invalid binaries, wrong arch, weird elf version. */
static int elf_header_check(struct load_info *info)
{
	if (info->len < sizeof(*(info->hdr)))
		return -ENOEXEC;

	if (memcmp(info->hdr->e_ident, ELFMAG, SELFMAG) != 0
	    || info->hdr->e_type != ET_REL
	    || !elf_check_arch(info->hdr)
	    || info->hdr->e_shentsize != sizeof(Elf_Shdr))
		return -ENOEXEC;

	if (info->hdr->e_shoff >= info->len
	    || (info->hdr->e_shnum * sizeof(Elf_Shdr) >
		info->len - info->hdr->e_shoff))
		return -ENOEXEC;

	return 0;
}

static void check_modinfo_retpoline(struct module *mod, struct load_info *info)
{
	if (retpoline_module_ok(get_modinfo(info, "retpoline")))
		return;

	pr_warn("%s: loading module not compiled with retpoline compiler.\n",
		mod->name);
}

static int rewrite_section_headers(struct load_info *info, int flags)
{
	unsigned int i;

	/* This should always be true, but let's be sure. */
	info->sechdrs[0].sh_addr = 0;

	for (i = 1; i < info->hdr->e_shnum; i++) {
		Elf_Shdr *shdr = &info->sechdrs[i];
		if (shdr->sh_type != SHT_NOBITS
		    && info->len < shdr->sh_offset + shdr->sh_size) {
			pr_err("Module len %lu truncated\n", info->len);
			return -ENOEXEC;
		}

		/* Mark all sections sh_addr with their address in the
		   temporary image. */
		shdr->sh_addr = (size_t)info->hdr + shdr->sh_offset;

#ifndef CONFIG_MODULE_UNLOAD
		/* Don't load .exit sections */
		if (module_exit_section(info->secstrings+shdr->sh_name))
			shdr->sh_flags &= ~(unsigned long)SHF_ALLOC;
#endif
	}

	/* Track but don't keep modinfo and version sections. */
	info->sechdrs[info->index.vers].sh_flags &= ~(unsigned long)SHF_ALLOC;
	info->sechdrs[info->index.info].sh_flags &= ~(unsigned long)SHF_ALLOC;

	return 0;
}

/*
 * Set up our basic convenience variables (pointers to section headers,
 * search for module section index etc), and do some basic section
 * verification.
 *
 * Set info->mod to the temporary copy of the module in info->hdr. The final one
 * will be allocated in move_module().
 */
static int setup_load_info(struct load_info *info, int flags)
{
	unsigned int i;

	/* Set up the convenience variables */
	info->sechdrs = (void *)info->hdr + info->hdr->e_shoff;
	info->secstrings = (void *)info->hdr
		+ info->sechdrs[info->hdr->e_shstrndx].sh_offset;

	/* Try to find a name early so we can log errors with a module name */
	info->index.info = find_sec(info, ".modinfo");
	if (info->index.info)
		info->name = get_modinfo(info, "name");

	/* Find internal symbols and strings. */
	for (i = 1; i < info->hdr->e_shnum; i++) {
		if (info->sechdrs[i].sh_type == SHT_SYMTAB) {
			info->index.sym = i;
			info->index.str = info->sechdrs[i].sh_link;
			info->strtab = (char *)info->hdr
				+ info->sechdrs[info->index.str].sh_offset;
			break;
		}
	}

	if (info->index.sym == 0) {
		pr_warn("%s: module has no symbols (stripped?)\n",
			info->name ?: "(missing .modinfo section or name field)");
		return -ENOEXEC;
	}

	info->index.mod = find_sec(info, ".gnu.linkonce.this_module");
	if (!info->index.mod) {
		pr_warn("%s: No module found in object\n",
			info->name ?: "(missing .modinfo section or name field)");
		return -ENOEXEC;
	}
	/* This is temporary: point mod into copy of data. */
	info->mod = (void *)info->hdr + info->sechdrs[info->index.mod].sh_offset;

	/*
	 * If we didn't load the .modinfo 'name' field earlier, fall back to
	 * on-disk struct mod 'name' field.
	 */
	if (!info->name)
		info->name = info->mod->name;

	if (flags & MODULE_INIT_IGNORE_MODVERSIONS)
		info->index.vers = 0; /* Pretend no __versions section! */
	else
		info->index.vers = find_sec(info, "__versions");

	info->index.pcpu = find_pcpusec(info);

	return 0;
}

static int check_modinfo(struct module *mod, struct load_info *info, int flags)
{
	const char *modmagic = get_modinfo(info, "vermagic");
	int err;

	if (flags & MODULE_INIT_IGNORE_VERMAGIC)
		modmagic = NULL;

	/* This is allowed: modprobe --force will invalidate it. */
	if (!modmagic) {
		err = try_to_force_load(mod, "bad vermagic");
		if (err)
			return err;
	}

	if (!get_modinfo(info, "intree")) {
		if (!test_taint(TAINT_OOT_MODULE))
			pr_warn("%s: loading out-of-tree module taints kernel.\n",
				mod->name);
		add_taint_module(mod, TAINT_OOT_MODULE, LOCKDEP_STILL_OK);
	}

	check_modinfo_retpoline(mod, info);

	if (get_modinfo(info, "staging")) {
		add_taint_module(mod, TAINT_CRAP, LOCKDEP_STILL_OK);
		pr_warn("%s: module is from the staging directory, the quality "
			"is unknown, you have been warned.\n", mod->name);
	}

	//err = check_modinfo_livepatch(mod, info);
	//if (err)
	//	return err;

	/* Set up license info based on the info section */
	//set_license(mod, get_modinfo(info, "license"));

	return 0;
}

static int find_module_sections(struct module *mod, struct load_info *info)
{
	mod->kp = section_objs(info, "__param",
			       sizeof(*mod->kp), &mod->num_kp);
	mod->syms = section_objs(info, "__ksymtab",
				 sizeof(*mod->syms), &mod->num_syms);
	mod->crcs = section_addr(info, "__kcrctab");
	mod->gpl_syms = section_objs(info, "__ksymtab_gpl",
				     sizeof(*mod->gpl_syms),
				     &mod->num_gpl_syms);
	mod->gpl_crcs = section_addr(info, "__kcrctab_gpl");
	mod->gpl_future_syms = section_objs(info,
					    "__ksymtab_gpl_future",
					    sizeof(*mod->gpl_future_syms),
					    &mod->num_gpl_future_syms);
	mod->gpl_future_crcs = section_addr(info, "__kcrctab_gpl_future");

#ifdef CONFIG_UNUSED_SYMBOLS
	mod->unused_syms = section_objs(info, "__ksymtab_unused",
					sizeof(*mod->unused_syms),
					&mod->num_unused_syms);
	mod->unused_crcs = section_addr(info, "__kcrctab_unused");
	mod->unused_gpl_syms = section_objs(info, "__ksymtab_unused_gpl",
					    sizeof(*mod->unused_gpl_syms),
					    &mod->num_unused_gpl_syms);
	mod->unused_gpl_crcs = section_addr(info, "__kcrctab_unused_gpl");
#endif
#ifdef CONFIG_CONSTRUCTORS
	mod->ctors = section_objs(info, ".ctors",
				  sizeof(*mod->ctors), &mod->num_ctors);
	if (!mod->ctors)
		mod->ctors = section_objs(info, ".init_array",
				sizeof(*mod->ctors), &mod->num_ctors);
	else if (find_sec(info, ".init_array")) {
		/*
		 * This shouldn't happen with same compiler and binutils
		 * building all parts of the module.
		 */
		pr_warn("%s: has both .ctors and .init_array.\n",
		       mod->name);
		return -EINVAL;
	}
#endif

	mod->noinstr_text_start = section_objs(info, ".noinstr.text", 1,
						&mod->noinstr_text_size);

#ifdef CONFIG_TRACEPOINTS
	mod->tracepoints_ptrs = section_objs(info, "__tracepoints_ptrs",
					     sizeof(*mod->tracepoints_ptrs),
					     &mod->num_tracepoints);
#endif
#ifdef CONFIG_TREE_SRCU
	mod->srcu_struct_ptrs = section_objs(info, "___srcu_struct_ptrs",
					     sizeof(*mod->srcu_struct_ptrs),
					     &mod->num_srcu_structs);
#endif
#ifdef CONFIG_BPF_EVENTS
	mod->bpf_raw_events = section_objs(info, "__bpf_raw_tp_map",
					   sizeof(*mod->bpf_raw_events),
					   &mod->num_bpf_raw_events);
#endif
#ifdef CONFIG_JUMP_LABEL
	mod->jump_entries = section_objs(info, "__jump_table",
					sizeof(*mod->jump_entries),
					&mod->num_jump_entries);
#endif
#ifdef CONFIG_EVENT_TRACING
	mod->trace_events = section_objs(info, "_ftrace_events",
					 sizeof(*mod->trace_events),
					 &mod->num_trace_events);
	mod->trace_evals = section_objs(info, "_ftrace_eval_map",
					sizeof(*mod->trace_evals),
					&mod->num_trace_evals);
#endif
#ifdef CONFIG_TRACING
	mod->trace_bprintk_fmt_start = section_objs(info, "__trace_printk_fmt",
					 sizeof(*mod->trace_bprintk_fmt_start),
					 &mod->num_trace_bprintk_fmt);
#endif
#ifdef CONFIG_FTRACE_MCOUNT_RECORD
	/* sechdrs[0].sh_size is always zero */
	mod->ftrace_callsites = section_objs(info, FTRACE_CALLSITE_SECTION,
					     sizeof(*mod->ftrace_callsites),
					     &mod->num_ftrace_callsites);
#endif
#ifdef CONFIG_FUNCTION_ERROR_INJECTION
	mod->ei_funcs = section_objs(info, "_error_injection_whitelist",
					    sizeof(*mod->ei_funcs),
					    &mod->num_ei_funcs);
#endif
#ifdef CONFIG_KPROBES
	mod->kprobes_text_start = section_objs(info, ".kprobes.text", 1,
						&mod->kprobes_text_size);
	mod->kprobe_blacklist = section_objs(info, "_kprobe_blacklist",
						sizeof(unsigned long),
						&mod->num_kprobe_blacklist);
#endif
#ifdef CONFIG_HAVE_STATIC_CALL_INLINE
	mod->static_call_sites = section_objs(info, ".static_call_sites",
					      sizeof(*mod->static_call_sites),
					      &mod->num_static_call_sites);
#endif
	mod->extable = section_objs(info, "__ex_table",
				    sizeof(*mod->extable), &mod->num_exentries);

	if (section_addr(info, "__obsparm"))
		pr_warn("%s: Ignoring obsolete parameters\n", mod->name);

	info->debug = section_objs(info, "__dyndbg",
				   sizeof(*info->debug), &info->num_debug);

	return 0;
}

static int move_module(struct module *mod, struct load_info *info)
{
	int i;
	void *ptr;

	/* Do the allocs. */
	ptr = module_alloc(mod->core_layout.size);
	/*
	 * The pointer to this block is stored in the module structure
	 * which is inside the block. Just mark it as not being a
	 * leak.
	 */
	kmemleak_not_leak(ptr);
	if (!ptr)
		return -ENOMEM;

	memset(ptr, 0, mod->core_layout.size);
	mod->core_layout.base = ptr;

	if (mod->init_layout.size) {
		ptr = module_alloc(mod->init_layout.size);
		/*
		 * The pointer to this block is stored in the module structure
		 * which is inside the block. This block doesn't need to be
		 * scanned as it contains data and code that will be freed
		 * after the module is initialized.
		 */
		kmemleak_ignore(ptr);
		if (!ptr) {
			module_memfree(mod->core_layout.base);
			return -ENOMEM;
		}
		memset(ptr, 0, mod->init_layout.size);
		mod->init_layout.base = ptr;
	} else
		mod->init_layout.base = NULL;

	/* Transfer each section which specifies SHF_ALLOC */
	pr_debug("final section addresses:\n");
	for (i = 0; i < info->hdr->e_shnum; i++) {
		void *dest;
		Elf_Shdr *shdr = &info->sechdrs[i];

		if (!(shdr->sh_flags & SHF_ALLOC))
			continue;

		if (shdr->sh_entsize & INIT_OFFSET_MASK)
			dest = mod->init_layout.base
				+ (shdr->sh_entsize & ~INIT_OFFSET_MASK);
		else
			dest = mod->core_layout.base + shdr->sh_entsize;

		if (shdr->sh_type != SHT_NOBITS)
			memcpy(dest, (void *)shdr->sh_addr, shdr->sh_size);
		/* Update sh_addr to point to copy in image. */
		shdr->sh_addr = (unsigned long)dest;
		pr_debug("\t0x%lx %s\n",
			 (long)shdr->sh_addr, info->secstrings + shdr->sh_name);
	}

	return 0;
}

static int check_module_license_and_versions(struct module *mod)
{
	int prev_taint = test_taint(TAINT_PROPRIETARY_MODULE);

	/*
	 * ndiswrapper is under GPL by itself, but loads proprietary modules.
	 * Don't use add_taint_module(), as it would prevent ndiswrapper from
	 * using GPL-only symbols it needs.
	 */
	if (strcmp(mod->name, "ndiswrapper") == 0)
		add_taint(TAINT_PROPRIETARY_MODULE, LOCKDEP_NOW_UNRELIABLE);

	/* driverloader was caught wrongly pretending to be under GPL */
	if (strcmp(mod->name, "driverloader") == 0)
		add_taint_module(mod, TAINT_PROPRIETARY_MODULE,
				 LOCKDEP_NOW_UNRELIABLE);

	/* lve claims to be GPL but upstream won't provide source */
	if (strcmp(mod->name, "lve") == 0)
		add_taint_module(mod, TAINT_PROPRIETARY_MODULE,
				 LOCKDEP_NOW_UNRELIABLE);

	if (!prev_taint && test_taint(TAINT_PROPRIETARY_MODULE))
		pr_warn("%s: module license taints kernel.\n", mod->name);

#ifdef CONFIG_MODVERSIONS
	if ((mod->num_syms && !mod->crcs)
	    || (mod->num_gpl_syms && !mod->gpl_crcs)
	    || (mod->num_gpl_future_syms && !mod->gpl_future_crcs)
#ifdef CONFIG_UNUSED_SYMBOLS
	    || (mod->num_unused_syms && !mod->unused_crcs)
	    || (mod->num_unused_gpl_syms && !mod->unused_gpl_crcs)
#endif
		) {
		return try_to_force_load(mod,
					 "no versions for exported symbols");
	}
#endif
	return 0;
}

static void flush_module_icache(const struct module *mod)
{
	/*
	 * Flush the instruction cache, since we've played with text.
	 * Do it before processing of module parameters, so the module
	 * can provide parameter accessor functions of its own.
	 */
	if (mod->init_layout.base)
		flush_icache_range((unsigned long)mod->init_layout.base,
				   (unsigned long)mod->init_layout.base
				   + mod->init_layout.size);
	flush_icache_range((unsigned long)mod->core_layout.base,
			   (unsigned long)mod->core_layout.base + mod->core_layout.size);
}

int __weak module_frob_arch_sections(Elf_Ehdr *hdr,
				     Elf_Shdr *sechdrs,
				     char *secstrings,
				     struct module *mod)
{
	return 0;
}

static struct module *layout_and_allocate(struct load_info *info, int flags)
{
	struct module *mod;
	unsigned int ndx;
	int err;

	err = check_modinfo(info->mod, info, flags);
	if (err)
		return ERR_PTR(err);

	/* Allow arches to frob section contents and sizes.  */
	err = module_frob_arch_sections(info->hdr, info->sechdrs,
					info->secstrings, info->mod);
	if (err < 0)
		return ERR_PTR(err);

	err = module_enforce_rwx_sections(info->hdr, info->sechdrs,
					  info->secstrings, info->mod);
	if (err < 0)
		return ERR_PTR(err);

	/* We will do a special allocation for per-cpu sections later. */
	info->sechdrs[info->index.pcpu].sh_flags &= ~(unsigned long)SHF_ALLOC;

	/*
	 * Mark ro_after_init section with SHF_RO_AFTER_INIT so that
	 * layout_sections() can put it in the right place.
	 * Note: ro_after_init sections also have SHF_{WRITE,ALLOC} set.
	 */
	ndx = find_sec(info, ".data..ro_after_init");
	if (ndx)
		info->sechdrs[ndx].sh_flags |= SHF_RO_AFTER_INIT;
	/*
	 * Mark the __jump_table section as ro_after_init as well: these data
	 * structures are never modified, with the exception of entries that
	 * refer to code in the __init section, which are annotated as such
	 * at module load time.
	 */
	ndx = find_sec(info, "__jump_table");
	if (ndx)
		info->sechdrs[ndx].sh_flags |= SHF_RO_AFTER_INIT;

	/* Determine total sizes, and put offsets in sh_entsize.  For now
	   this is done generically; there doesn't appear to be any
	   special cases for the architectures. */
	layout_sections(info->mod, info);
	layout_symtab(info->mod, info);

	/* Allocate and move to the final place */
	err = move_module(info->mod, info);
	if (err)
		return ERR_PTR(err);

	/* Module has been copied to its final place now: return it. */
	mod = (void *)info->sechdrs[info->index.mod].sh_addr;
	return mod;
}

/* mod is no longer valid after this! */
static void module_deallocate(struct module *mod, struct load_info *info)
{
	percpu_modfree(mod);
	module_arch_freeing_init(mod);
	module_memfree(mod->init_layout.base);
	module_memfree(mod->core_layout.base);
}

int __weak module_finalize(const Elf_Ehdr *hdr,
			   const Elf_Shdr *sechdrs,
			   struct module *me)
{
	return 0;
}

static int post_relocation(struct module *mod, const struct load_info *info)
{
	/* Sort exception table now relocations are done. */
	sort_extable(mod->extable, mod->extable + mod->num_exentries);

	/* Copy relocated percpu area over. */
	percpu_modcopy(mod, (void *)info->sechdrs[info->index.pcpu].sh_addr,
		       info->sechdrs[info->index.pcpu].sh_size);

	/* Setup kallsyms-specific fields. */
	add_kallsyms(mod, info);

	/* Arch-specific module finalizing. */
	return module_finalize(info->hdr, info->sechdrs, mod);
}

/* Is this module of this name done loading?  No locks held. */
static bool finished_loading(const char *name)
{
	struct module *mod;
	bool ret;

	/*
	 * The module_mutex should not be a heavily contended lock;
	 * if we get the occasional sleep here, we'll go an extra iteration
	 * in the wait_event_interruptible(), which is harmless.
	 */
	sched_annotate_sleep();
	mutex_lock(&module_mutex);
	mod = find_module_all(name, strlen(name), true);
	ret = !mod || mod->state == MODULE_STATE_LIVE;
	mutex_unlock(&module_mutex);

	return ret;
}

/* Call module constructors. */
static void do_mod_ctors(struct module *mod)
{
#ifdef CONFIG_CONSTRUCTORS
	unsigned long i;

	for (i = 0; i < mod->num_ctors; i++)
		mod->ctors[i]();
#endif
}

/* For freeing module_init on success, in case kallsyms traversing */
struct mod_initfree {
	struct llist_node node;
	void *module_init;
};

static void do_free_init(struct work_struct *w)
{
	struct llist_node *pos, *n, *list;
	struct mod_initfree *initfree;

	list = llist_del_all(&init_free_list);

	synchronize_rcu();

	llist_for_each_safe(pos, n, list) {
		initfree = container_of(pos, struct mod_initfree, node);
		module_memfree(initfree->module_init);
		kfree(initfree);
	}
}

/*
 * This is where the real work happens.
 *
 * Keep it uninlined to provide a reliable breakpoint target, e.g. for the gdb
 * helper command 'lx-symbols'.
 */
static noinline int do_init_module(struct module *mod)
{
	int ret = 0;
	struct mod_initfree *freeinit;

	freeinit = kmalloc(sizeof(*freeinit), GFP_KERNEL);
	if (!freeinit) {
		ret = -ENOMEM;
		goto fail;
	}
	freeinit->module_init = mod->init_layout.base;

	/*
	 * We want to find out whether @mod uses async during init.  Clear
	 * PF_USED_ASYNC.  async_schedule*() will set it.
	 */
	current->flags &= ~PF_USED_ASYNC;

	do_mod_ctors(mod);
	/* Start the module */
	if (mod->init != NULL)
		ret = do_one_initcall(mod->init);
	if (ret < 0) {
		goto fail_free_freeinit;
	}
	if (ret > 0) {
		pr_warn("%s: '%s'->init suspiciously returned %d, it should "
			"follow 0/-E convention\n"
			"%s: loading module anyway...\n",
			__func__, mod->name, ret, __func__);
		dump_stack();
	}

	/* Now it's a first class citizen! */
	mod->state = MODULE_STATE_LIVE;
	blocking_notifier_call_chain(&module_notify_list,
				     MODULE_STATE_LIVE, mod);

	/* Delay uevent until module has finished its init routine */
	kobject_uevent(&mod->mkobj.kobj, KOBJ_ADD);

	/*
	 * We need to finish all async code before the module init sequence
	 * is done.  This has potential to deadlock.  For example, a newly
	 * detected block device can trigger request_module() of the
	 * default iosched from async probing task.  Once userland helper
	 * reaches here, async_synchronize_full() will wait on the async
	 * task waiting on request_module() and deadlock.
	 *
	 * This deadlock is avoided by perfomring async_synchronize_full()
	 * iff module init queued any async jobs.  This isn't a full
	 * solution as it will deadlock the same if module loading from
	 * async jobs nests more than once; however, due to the various
	 * constraints, this hack seems to be the best option for now.
	 * Please refer to the following thread for details.
	 *
	 * http://thread.gmane.org/gmane.linux.kernel/1420814
	 */
	if (!mod->async_probe_requested && (current->flags & PF_USED_ASYNC))
		async_synchronize_full();

	ftrace_free_mem(mod, mod->init_layout.base, mod->init_layout.base +
			mod->init_layout.size);
	mutex_lock(&module_mutex);
	/* Drop initial reference. */
	module_put(mod);
	trim_init_extable(mod);
#ifdef CONFIG_KALLSYMS
	/* Switch to core kallsyms now init is done: kallsyms may be walking! */
	rcu_assign_pointer(mod->kallsyms, &mod->core_kallsyms);
#endif
	module_enable_ro(mod, true);
	mod_tree_remove_init(mod);
	module_arch_freeing_init(mod);
	mod->init_layout.base = NULL;
	mod->init_layout.size = 0;
	mod->init_layout.ro_size = 0;
	mod->init_layout.ro_after_init_size = 0;
	mod->init_layout.text_size = 0;
	/*
	 * We want to free module_init, but be aware that kallsyms may be
	 * walking this with preempt disabled.  In all the failure paths, we
	 * call synchronize_rcu(), but we don't want to slow down the success
	 * path. module_memfree() cannot be called in an interrupt, so do the
	 * work and call synchronize_rcu() in a work queue.
	 *
	 * Note that module_alloc() on most architectures creates W+X page
	 * mappings which won't be cleaned up until do_free_init() runs.  Any
	 * code such as mark_rodata_ro() which depends on those mappings to
	 * be cleaned up needs to sync with the queued work - ie
	 * rcu_barrier()
	 */
	if (llist_add(&freeinit->node, &init_free_list))
		schedule_work(&init_free_wq);

	mutex_unlock(&module_mutex);
	wake_up_all(&module_wq);

	return 0;

fail_free_freeinit:
	kfree(freeinit);
fail:
	/* Try to protect us from buggy refcounters. */
	mod->state = MODULE_STATE_GOING;
	synchronize_rcu();
	module_put(mod);
	blocking_notifier_call_chain(&module_notify_list,
				     MODULE_STATE_GOING, mod);
	klp_module_going(mod);
	ftrace_release_mod(mod);
	free_module(mod);
	wake_up_all(&module_wq);
	return ret;
}


/*
 * We try to place it in the list now to make sure it's unique before
 * we dedicate too many resources.  In particular, temporary percpu
 * memory exhaustion.
 */
static int add_unformed_module(struct module *mod)
{
	int err;
	struct module *old;

	mod->state = MODULE_STATE_UNFORMED;

again:
	mutex_lock(&module_mutex);
	old = find_module_all(mod->name, strlen(mod->name), true);
	if (old != NULL) {
		if (old->state != MODULE_STATE_LIVE) {
			/* Wait in case it fails to load. */
			mutex_unlock(&module_mutex);
			err = wait_event_interruptible(module_wq,
					       finished_loading(mod->name));
			if (err)
				goto out_unlocked;
			goto again;
		}
		err = -EEXIST;
		goto out;
	}
	mod_update_bounds(mod);
	list_add_rcu(&mod->list, &injection_modules);
	mod_tree_insert(mod);
	err = 0;

out:
	mutex_unlock(&module_mutex);
out_unlocked:
	return err;
}

static int complete_formation(struct module *mod, struct load_info *info)
{
	int err;

	mutex_lock(&module_mutex);

	/* Find duplicate symbols (must be called under lock). */
	err = verify_exported_symbols(mod);
	if (err < 0)
		goto out;

	/* This relies on module_mutex for list integrity. */
	module_bug_finalize(info->hdr, info->sechdrs, mod);

	module_enable_ro(mod, false);
	module_enable_nx(mod);
	module_enable_x(mod);

	/* Mark state as coming so strong_try_module_get() ignores us,
	 * but kallsyms etc. can see us. */
	mod->state = MODULE_STATE_COMING;
	mutex_unlock(&module_mutex);

	return 0;

out:
	mutex_unlock(&module_mutex);
	return err;
}

static int prepare_coming_module(struct module *mod)
{
	int err;

	ftrace_module_enable(mod);
	err = klp_module_coming(mod);
	if (err)
		return err;

	err = blocking_notifier_call_chain_robust(&module_notify_list,
			MODULE_STATE_COMING, MODULE_STATE_GOING, mod);
	err = notifier_to_errno(err);
	if (err)
		klp_module_going(mod);

	return err;
}

/* Allocate and load the module: note that size of section 0 is always
   zero, and we rely on this for optional sections. */
int injection_load_module(struct load_info *info, int flags)
{
	struct module *mod;
	long err = 0;

	err = elf_header_check(info);
	if (err) {
		pr_err("Module has invalid ELF header\n");
		goto out;
	}

	err = setup_load_info(info, flags);
	if (err)
		goto out;

	err = rewrite_section_headers(info, flags);
	if (err)
		goto out;

	/* Check module struct version now, before we try to use module. */
	//if (!check_modstruct_version(info, info->mod)) {
	//	err = -ENOEXEC;
	//	goto out;
	//}

	/* Figure out module layout, and allocate all the memory. */
	mod = layout_and_allocate(info, flags);
	if (IS_ERR(mod)) {
		err = PTR_ERR(mod);
		goto out;
	}

	/* Reserve our place in the list. */
	err = add_unformed_module(mod);
	if (err)
		goto free_module;

	/* To avoid stressing percpu allocator, do this once we're unique. */
	err = percpu_modalloc(mod, info);
	if (err)
		goto unlink_mod;

	init_param_lock(mod);

	/* Now we've got everything in the final locations, we can
	 * find optional sections. */
	err = find_module_sections(mod, info);
	if (err)
		goto free_unload;

	err = check_module_license_and_versions(mod);
	if (err)
		goto free_unload;

	/* Set up MODINFO_ATTR fields */
	setup_modinfo(mod, info);

	/* Fix up syms, so that st_value is a pointer to location. */
	err = simplify_symbols(mod, info);
	if (err < 0)
		goto free_modinfo;

	err = apply_relocations(mod, info);
	if (err < 0)
		goto free_modinfo;

	err = post_relocation(mod, info);
	if (err < 0)
		goto free_modinfo;

	flush_module_icache(mod);

	/* Now copy in args */
	mod->args = NULL;

	dynamic_debug_setup(mod, info->debug, info->num_debug);

	/* Ftrace init must be called in the MODULE_STATE_UNFORMED state */
	ftrace_module_init(mod);

	/* Finally it's fully formed, ready to start executing. */
	err = complete_formation(mod, info);
	if (err)
		goto ddebug_cleanup;

	err = prepare_coming_module(mod);
	if (err)
		goto bug_cleanup;

	/* Link in to sysfs. */
	err = mod_sysfs_setup(mod, info, mod->kp, mod->num_kp);
	if (err < 0)
		goto coming_cleanup;

//	if (is_livepatch_module(mod)) {
//		err = copy_module_elf(mod, info);
//		if (err < 0)
//			goto sysfs_cleanup;
//	}

	/* Done! */
	trace_module_load(mod);

	return do_init_module(mod);

 sysfs_cleanup:
	mod_sysfs_teardown(mod);
 coming_cleanup:
	mod->state = MODULE_STATE_GOING;
	destroy_params(mod->kp, mod->num_kp);
	blocking_notifier_call_chain(&module_notify_list,
				     MODULE_STATE_GOING, mod);
	klp_module_going(mod);
 bug_cleanup:
	mod->state = MODULE_STATE_GOING;
	/* module_bug_cleanup needs module_mutex protection */
	mutex_lock(&module_mutex);
	module_bug_cleanup(mod);
	mutex_unlock(&module_mutex);

 ddebug_cleanup:
	ftrace_release_mod(mod);
	dynamic_debug_remove(mod, info->debug);
	synchronize_rcu();
	kfree(mod->args);
	module_arch_cleanup(mod);
 free_modinfo:
	free_modinfo(mod);
 free_unload:
 unlink_mod:
	mutex_lock(&module_mutex);
	/* Unlink carefully: kallsyms could be walking list. */
	list_del_rcu(&mod->list);
	mod_tree_remove(mod);
	wake_up_all(&module_wq);
	/* Wait for RCU-sched synchronizing before releasing mod->list. */
	synchronize_rcu();
	mutex_unlock(&module_mutex);
 free_module:
	/* Free lock-classes; relies on the preceding sync_rcu() */
	lockdep_free_key_range(mod->core_layout.base, mod->core_layout.size);

	module_deallocate(mod, info);
 out:
	return err;
}
EXPORT_SYMBOL(injection_load_module);
