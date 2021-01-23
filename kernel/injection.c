#define DEBUG
#define pr_fmt(fmt)	"injection: " fmt

#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/uaccess.h>
#include <linux/kallsyms.h>
#include <linux/miscdevice.h>
#include <linux/proc_fs.h>
#include <linux/atomic.h>
#include <linux/slab.h>

#include <asm/e820/api.h>
#include <asm/io.h>

struct load_info;

#define MAGIC	0x20210122

typedef int (*load_module_t)(struct load_info *, const char __user *, int);
static load_module_t do_load_module;

static unsigned long phys_addr;
static unsigned long mem_size;
static void *virt_addr;
static bool mem_clear;
static atomic_long_t dev_offset;
static size_t dev_init_offset;

static int __init do_injection(void)
{
	char *buf = NULL;
	int len = 0;

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

	do_load_module = (load_module_t)kallsyms_lookup_name("load_module");
	if (do_load_module == NULL) {
		pr_warn("%s: not found symbol 'do_load_module'", __func__);
		return 0;
	}

	buf = virt_addr;
	while (*(int *)(buf+dev_init_offset) == MAGIC) {
		dev_init_offset += sizeof(int);
		len = *(int *)(buf + dev_init_offset);
		dev_init_offset += sizeof(int);

		if (do_load_module((struct load_info *)(buf+dev_init_offset), NULL, 0) != 0)
			pr_warn("load_module failed\n");

		dev_init_offset += len;
	}

out:
	atomic_long_set(&dev_offset, dev_init_offset);
	return 0;
}
early_initcall(do_injection);

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

enum injection_status {
	INJECTION_BEGIN,
	INJECTION_COMPLETE,
	INJECTION_BAD,
};

struct injection_info {
	enum injection_status status;
	char *base;
	size_t offset;
	size_t total_len;
};

static int injection_open(struct inode *inode, struct file *filp)
{
	struct injection_info *info;
	size_t offset;

	if (!(filp->f_mode & O_APPEND)) {
		atomic_long_set(&dev_offset, dev_init_offset);
	}

	if (!!(filp->f_mode & FMODE_WRITE)) {
	} else if (!!(filp->f_mode & FMODE_READ)) {
	}

	info = kzalloc(sizeof(struct injection_info), GFP_KERNEL);
	if (info == NULL)
		return -ENOMEM;

	offset = atomic_long_read(&dev_offset);
	if ((offset+sizeof(int)*2) >= mem_size)
		return -ENOMEM;

	info->status = INJECTION_BEGIN;
	info->base = ((char *)virt_addr) + offset;
	info->offset = sizeof(int) * 2; /* magic + len */
	info->total_len = mem_size;
	filp->private_data = info;

	return 0;
}

static ssize_t injection_read(struct file *filp, char __user *buf,
			      size_t count, loff_t *offp)
{
	// 1. write content
	// 2. set len
	// 3. set magic
	return 0;
}

static ssize_t injection_write(struct file *filp, const char __user *buf,
			      size_t count, loff_t *offp)
{
	struct injection_info *info = filp->private_data;
	int retval;

	if ((info->offset+count) > info->total_len)
		return -ENOMEM;

	retval = copy_from_user(info->base+info->offset, buf, count);
		return retval;

	info->offset += count;
	info->status = INJECTION_COMPLETE;

	return count;
}

static int injection_release(struct inode *inode, struct file *filp)
{
	struct injection_info *info = filp->private_data;
	char *base = info->base;

	if (info->status != INJECTION_COMPLETE)
		goto out;

	*(int *)base = MAGIC;
	*(int *)(base+sizeof(int)) = info->offset - 2 * sizeof(int);
	*(int *)(base+info->offset) = 0;

	atomic_long_add(info->offset, &dev_offset);
out:
	kfree(info);
	return 0;
}

static const struct file_operations injection_dev_ops = {
	.owner = THIS_MODULE,
	.open = injection_open,
	.write = injection_write,
	.read = injection_read,
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
