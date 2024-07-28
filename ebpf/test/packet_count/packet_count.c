#include <linux/types.h>
#include <asm/types.h>
#include <inttypes.h>
#include <stdint.h>
//#include <linux/bpf.h>
//#include <bpf/bpf_helpers.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf/bpf_helpers.h>

/*enum xdp_action {
	XDP_ABORTED = 0,
	XDP_DROP,
	XDP_PASS,
	XDP_TX,
	XDP_REDIRECT,
};*/

//static long (* const bpf_trace_printk)(const char *fmt, __u32 fmt_size, ...) = (void *) 6;

/*
#undef bpf_printk
#define bpf_printk(fmt, ...)                           \
{                                                      \
        char ____fmt[] = fmt;                           \
        bpf_trace_printk(____fmt, sizeof(____fmt),      \
                         ##__VA_ARGS__);                \
}*/

#undef SEC
#define SEC(A) __attribute__ ((section(A),used))

int counter = 0;

SEC("xdp")
int packet_count(void *ctx) {
    bpf_printk("%d", counter);
    counter = counter + 1;
    return XDP_PASS;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";


// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/packet_count.s ebpf/test/packet_count/packet_count.c 

// file ebpf/test/packet_count.o
// ELF 64-bit LSB relocatable, eBPF, version 1 (SYSV), with     debug_info, not stripped

/* llvm-objdump ebpf/test/packet_count.o
ebpf/test/packet_count/packet_count.o:  file format elf64-bpf

Disassembly of section .text:

0000000000000000 <packet_count>:
       0:       bf a0 00 00 00 00 00 00 r0 = r10
       1:       17 0a 00 00 10 00 00 00 r10 -= 16
       2:       7b 0a 00 00 00 00 00 00 *(u64 *)(r10 + 0) = r0
       3:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
       5:       b4 02 00 00 03 00 00 00 w2 = 3
       6:       18 03 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r3 = 0 ll
       8:       61 33 00 00 00 00 00 00 r3 = *(u32 *)(r3 + 0)
       9:       85 10 00 00 ff ff ff ff call -1
      10:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
      12:       61 10 00 00 00 00 00 00 r0 = *(u32 *)(r1 + 0)
      13:       04 00 00 00 01 00 00 00 w0 += 1
      14:       63 01 00 00 00 00 00 00 *(u32 *)(r1 + 0) = r0
      15:       b4 00 00 00 02 00 00 00 w0 = 2
      16:       07 0a 00 00 10 00 00 00 r10 += 16
      17:       95 00 00 00 00 00 00 00 exit */

/* sudo bpftool prog load ebpf/test/packet_count/packet_count.o  /sys/fs/bpf/packet_count
libbpf: elf: skipping unrecognized data section(6) .eh_frame
libbpf: elf: skipping relo section(7) .rel.eh_frame for section(6) .eh_frame
libbpf: failed to find BTF for extern 'bpf_trace_printk': -3
Error: failed to open object file */