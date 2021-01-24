#!/bin/bash

qemu-system-x86_64  \
    -smbios type=0,uefi=on   \
    -machine pc   \
    -smp 1   \
    -m  4G \
    -boot menu=on \
    -object rng-random,filename=/dev/urandom,id=rng0 \
    -device virtio-rng-pci,rng=rng0 \
    -drive if=none,file=vda.qcow2,format=qcow2,id=vda   \
    -device virtio-blk-pci,drive=vda \
    -netdev bridge,id=net0,br=virbr0 \
    -device virtio-net-pci,netdev=net0 \
    -chardev stdio,id=charchannel0 \
    -device isa-serial,chardev=charchannel0,id=serial0 \
    -fsdev local,id=fs1,path=/home/me,security_model=none \
    -device virtio-9p-pci,fsdev=fs1,mount_tag=host  \
    -append "root=/dev/vda1 console=ttyS0 log_level=8 injection_mem=64M@0x03000000" \
    -kernel bzImage \
    -display none   \
    -vnc 0.0.0.0:0  \
    -s
