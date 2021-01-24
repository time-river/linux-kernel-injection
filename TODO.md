TODO:

1. `late_initcall(do_injection);` --> `early_initcall(do_injection)`
   - Problem:
     * livepatch is not initialized, so we can't use livepatch inftra.
2. decoupling `kernel/module.c`, some process can't be used, like `strndup_user()` in `load_module()`
3. BUG in `injection_read()`

Reference:
1. [Github/freelancer-leon/notes: ftrace-design](https://github.com/freelancer-leon/notes/blob/master/kernel/trace/ftrace-design.md)
2. [Linux doc: Using ftrace to hook to functions](https://github.com/torvalds/linux/blob/master/Documentation/trace/ftrace-uses.rst)
3. [[RFC,2/2] kpatch: add kpatch core module](https://lore.kernel.org/patchwork/patch/461065/)
4. [Linux src: livepatch-sample.c](https://github.com/torvalds/linux/blob/master/samples/livepatch/livepatch-sample.c)
