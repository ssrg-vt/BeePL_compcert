#include <linux/types.h>
#include <asm/types.h>
#include <inttypes.h>
#include <stdint.h>
//#include <linux/bpf.h>
//#include <bpf/bpf_helpers.h>
#include <stdio.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf/bpf_helpers.h>
/*
#undef bpf_printk
#define bpf_printk(fmt, ...)                           \
{                                                      \
        char ____fmt[] = fmt;                           \
        bpf_trace_printk(____fmt, sizeof(____fmt),      \
                         ##__VA_ARGS__);                \
}*/


int main() {
    int i = 1;
    while(i < 2) {
        bpf_printk("temination_check");
        i++;
    }
    return 0;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/termination_check/termination_check.s ebpf/test/termination_check/termination_check.c 

// ./ccomp -D __bpf_helper_as_extern__ -interp ebpf/test/termination_check/termination_check.c