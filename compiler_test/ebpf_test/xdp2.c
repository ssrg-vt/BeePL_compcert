#include "/home/swarnp/research/BeePL_compcert/ebpf/lib/bpf.h"
#include "/home/swarnp/research/BeePL_compcert/ebpf/lib/bpf/bpf_helpers.h"

/*
#undef SEC
// bpf_helpers.h
#define SEC(NAME) __attribute__((section(NAME), used))

#undef bpf_printk
static int (*bpf_trace_printk)(const char *fmt, int fmt_size, ...) = (void *)6;
#define bpf_printk(fmt, ...)                          \
{                                                    \
    char ____fmt[] = fmt;                             \
    bpf_trace_printk(____fmt, sizeof(____fmt),        \
                     ##__VA_ARGS__);                  \
}*/

int val = 0;
int* counter = &val;

SEC("xdp")
int packet_count(void *ctx) {
    bpf_printk("%d", counter);
    *counter = *counter + 1;
    return XDP_PASS;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";

