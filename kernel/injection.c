#define DEBUG
#define pr_fmt(fmt)	"injection: " fmt

#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/uaccess.h>
#include <linux/miscdevice.h>
#include <linux/proc_fs.h>
#include <linux/atomic.h>
#include <linux/slab.h>
#include <linux/vmalloc.h>
#include <linux/mutex.h>
#include <crypto/md5.h>
#include <crypto/hash.h>
#include <linux/ftrace.h>
#include <linux/livepatch.h>

#include <asm/e820/api.h>
#include <asm/io.h>

#include "module-internal.h"

#define MAGIC	0x20210122

int load_module(struct load_info *, const char __user *, int);

static unsigned long phys_addr;
static unsigned long mem_size;
static void *virt_addr;
static bool mem_clear;
static atomic_long_t dev_offset;
static size_t dev_init_offset;

struct injection_ops {
	struct klp_func kfunc;
	struct ftrace_ops fops;
};

static void notrace ftrace_handler(unsigned long ip,
			       unsigned long parent_ip,
			       struct ftrace_ops *fops,
			       struct pt_regs *regs)
{
	struct injection_ops *ops;
	struct klp_func *kfunc;

	ops = container_of(fops, struct injection_ops, fops);
	kfunc = &ops->kfunc;

	if (kfunc->nop)
		return;

	klp_arch_set_pc(regs, (unsigned long)kfunc->new_func);
}

/*  run before smp() init, so we don't consider multi-thread. */
static int __init __do_injection(struct klp_func *func)
{
	struct injection_ops *kops;
	unsigned long ftrace_loc;
	int retval;

	kops = kzalloc(sizeof(*kops), GFP_KERNEL);
	if (!kops)
		return -ENOMEM;

	ftrace_loc = (unsigned long)func->old_func;

	kops->fops.func = ftrace_handler;
	kops->fops.flags = FTRACE_OPS_FL_SAVE_REGS |
			FTRACE_OPS_FL_DYNAMIC |
			FTRACE_OPS_FL_IPMODIFY |
			FTRACE_OPS_FL_PERMANENT;

	retval = ftrace_set_filter_ip(&kops->fops, ftrace_loc, 0, 0);
	if (retval != 0) {
		pr_err("%s: failed to set ftrace filter for function '%s' (%d)\n",
		       __func__, func->old_name, retval);
		goto error;
	}

	retval = register_ftrace_function(&kops->fops);
	if (retval != 0) {
		pr_err("%s: failed to register ftrace handler for function '%s' (%d)\n",
		       __func__, func->old_name, retval);
		ftrace_set_filter_ip(&kops->fops, ftrace_loc, 1, 0);
		goto error;
	}

	return 0;

error:
	kfree(kops);
	return retval;
}

static int __init do_injection(void)
{
	char *buf = NULL;
	int retval;

	if (phys_addr == 0 || mem_size == 0)
		return 0;

	virt_addr = ioremap(phys_addr, mem_size);
	if (virt_addr == NULL) {
		pr_info("%s: ioremap failed\n", __func__);
		return 0;
	}
	pr_info("reserved virtual memory range [0x%lx, 0x%lx)\n",
			(unsigned long)virt_addr,
			(unsigned long)(virt_addr+mem_size));

	if (mem_clear) {
		pr_info("clear memory\n");
		memset(virt_addr, 0, mem_size);
		goto out;
	} else
		pr_info("inject modules\n");

	buf = virt_addr;
	while (*(int *)(buf+dev_init_offset) == MAGIC) {
		struct load_info info = {};
		dev_init_offset += sizeof(int);
		info.len = *(int *)(buf + dev_init_offset);
		dev_init_offset += sizeof(int);

		//TODO: parse kernel module
		info.hdr = __vmalloc(info.len, GFP_KERNEL | __GFP_NOWARN);
		if (!info.hdr) {
			pr_warn("%s: no memory to alloc for module\n", __func__);
			return 0;
		}
		memcpy(info.hdr, buf+dev_init_offset, info.len);
		retval = load_module(&info, NULL, 0);
		if (retval != 0)
			pr_warn("load_module failed, retval=%d\n", retval);

		dev_init_offset += info.len;
	}

out:
	pr_info("%s: set devoffset 0x%zx\n", __func__, dev_init_offset);
	atomic_long_set(&dev_offset, dev_init_offset);
	return 0;
}
late_initcall(do_injection);

static int __init injection_opt(char *buf)
{
	char *p = buf;

	if (!p)
		return -EINVAL;

	mem_size = memparse(p, &p);
	if (p == buf)
		return -EINVAL;

	if (*p == '@')
		phys_addr = memparse(p+1, &p);

	e820__range_add(phys_addr, mem_size, E820_TYPE_RESERVED);
	pr_info("reserve physical memory range [0x%lx, 0x%lx)\n",
		phys_addr, phys_addr+mem_size);

	if (*p == ':')
		strtobool(p+1, &mem_clear);

	return 0;
}
early_param("injection_mem", injection_opt);

struct injection_info {
	char *base;
	size_t total_len;
	union {
		size_t offset;
		struct crypto_shash *tfm;
	};
};

DEFINE_MUTEX(injection_dev_lock);

static int injection_open(struct inode *inode, struct file *filp)
{
	struct injection_info *info;
	size_t offset, retval;

	info = kzalloc(sizeof(struct injection_info), GFP_KERNEL);
	if (info == NULL) {
		retval = -ENOMEM;
		goto error;
	}

	mutex_lock(&injection_dev_lock);
	if (!!(filp->f_mode & FMODE_WRITE)) {
		if (!(filp->f_mode & O_APPEND)) {
			atomic_long_set(&dev_offset, dev_init_offset);
			memset(virt_addr+dev_init_offset, 0, mem_size-dev_init_offset);
			offset = dev_init_offset;
		} else
			offset = atomic_long_read(&dev_offset);

		if ((offset+sizeof(int)*2) >= mem_size) {
			retval = -ENOMEM;
			goto error;
		}

		info->base = ((char *)virt_addr) + offset;
		info->offset = sizeof(int) * 2; /* magic + len */
		info->total_len = mem_size - offset - info->offset;
		filp->f_mode &= ~(FMODE_READ);
	} else if (!!(filp->f_mode & FMODE_READ)) {
		info->base = virt_addr;
		info->total_len = atomic_long_read(&dev_offset);
		info->tfm = crypto_alloc_shash("md5", 0, CRYPTO_ALG_ASYNC);
		if (IS_ERR(info->tfm)) {
			retval = PTR_ERR(info->tfm);
			goto error;
		}

		filp->f_mode &= ~(FMODE_WRITE);
	}

	pr_err(">>> %s: private_data=0x%lx info=0x%lx total_len=%ld\n",
	       __func__,
	       (unsigned long)filp->private_data,
	       (unsigned long)info,
	       info->total_len);
	filp->private_data = info;

	return 0;
error:
	kfree(info);
	return -ENOMEM;
}

static void md5_to_hex(char *out, u8 *md5)
{
	int i;

	for (i = 0; i < MD5_DIGEST_SIZE; i++) {
		unsigned char c = md5[i];

		*out++ = '0' + ((c&0xf0)>>4) + (c>=0xa0)*('a'-'9'-1);
		*out++ = '0' + (c&0x0f) + ((c&0x0f)>=0x0a)*('a'-'9'-1);
	}
	*out = '\n';
	*(out+1) = '\0';
}

// TODO: BUG here
static ssize_t injection_read(struct file *filp, char __user *buf,
			      size_t count, loff_t *offp)
{
	struct injection_info *info = filp->private_data;
	char *base = info->base, digest[MD5_DIGEST_SIZE+2] = {'\0'};
	ssize_t offset = 0, len = 0, read_bytes = 0, retval = 0;
	u8 md5[MD5_DIGEST_SIZE];

	pr_err("%s: header 0x%x len %d offset=%ld\n", __func__,
		 *(int *)base,
		 *(int *)(base + sizeof(int)),
		 offset);

	while (((offset+2*sizeof(int)) < info->total_len)
			&& (*(int *)(base+offset) == MAGIC)
			&& ((read_bytes+sizeof(digest)) < count)) {
		offset += sizeof(int);
		len = *(int *)(base+offset);
		offset += sizeof(int);

		pr_err(">>> 1: %x 2: %x 3: %x 4: %x -4: %x -3: %x -2: %x -1: %x\n",
		       base[offset], base[offset+1], base[offset+2], base[offset+3],
		       base[offset+len-40], base[offset+len-39],
		       base[offset+len-32], base[offset+len-16]);

		// TODO: md5sum is not right
		retval = crypto_shash_tfm_digest(info->tfm,
						 (u8 *)(base+offset), len, md5);
		if (retval)
			goto out;

		md5_to_hex(digest, md5);
		pr_err(">>> %s: md5 '%s'\n", __func__, digest);
	//	retval = copy_to_user(buf, digest, MD5_DIGEST_SIZE+1);
	//	if (retval)
	//		goto out;

		read_bytes += MD5_DIGEST_SIZE+1;
		offset += len;
		return read_bytes;
	}

	pr_err("%s: retval = %zd\n", __func__, read_bytes);
	retval = read_bytes;

out:
	return retval;
}

static ssize_t injection_write(struct file *filp, const char __user *buf,
			      size_t count, loff_t *offp)
{
	struct injection_info *info = filp->private_data;
	int retval;

	pr_err(">>> %s: offset=%ld count=%ld total_len=%ld\n", __func__,
	       info->offset, count, info->total_len);
	if (count > info->total_len) {
		pr_info("%s: no enough memory left, write %ld valid %ld\n",
			__func__, info->offset+count, info->total_len);
		return -ENOMEM;
	}

	retval = copy_from_user(info->base+info->offset, buf, count);
	if (retval) {
		pr_info("%s: copy_from_user() failed, retval=%d\n",
			__func__, retval);
		return retval;
	}
	info->offset += count;

	return count;
}

static int injection_close(struct file *filp, fl_owner_t fd)
{
	struct injection_info *info = filp->private_data;
	char *base = info->base;

	if (!!(filp->f_mode & FMODE_WRITE) && (info->offset > sizeof(int)*2)) {
		*(int *)base = MAGIC;
		*(int *)(base+sizeof(int)) = info->offset - 2 * sizeof(int);
		*(int *)(base+info->offset) = 0;

		atomic_long_add(info->offset, &dev_offset);
	}

	mutex_unlock(&injection_dev_lock);
	pr_err(">>> %s: offset=%ld dev_offset=%ld\n", __func__,
	       info->offset, atomic_long_read(&dev_offset));
	pr_devel(">>> %s: header 0x%x len %d 0x%lx\n", __func__,
		 *(int *)base,
		 *(int *)(base + sizeof(int)),
		 *(unsigned long *)(base+sizeof(int)*2));

	return 0;
}

static int injection_release(struct inode *inode, struct file *filp)
{
	struct injection_info *info = filp->private_data;
	if (!!(filp->f_mode & FMODE_READ))
		crypto_free_shash(info->tfm);
	// TODO: why need here?
	// set close would result crash
	// in open, private_data have value
	kfree(info);
	return 0;
}

static const struct file_operations injection_dev_ops = {
	.owner = THIS_MODULE,
	.open = injection_open,
	.write = injection_write,
	.read = injection_read,
	.flush = injection_close,
	.release = injection_release,
};

static struct miscdevice injection_dev = {
	.minor = MISC_DYNAMIC_MINOR,
	.name = "injection",
	.fops = &injection_dev_ops,
};

static int __init injection_device_init(void)
{
	// TODO: judge valide region
	//       clear memory
	return misc_register(&injection_dev);
}
device_initcall(injection_device_init);
