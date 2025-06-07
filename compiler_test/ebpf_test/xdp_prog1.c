#include <linux/types.h>
#include <asm/types.h>
#include <inttypes.h>
#include <stdint.h>
//#include <linux/bpf.h>
//#include <bpf/bpf_helpers.h>
#include <bpf.h>
#include <bpf/bpf_helpers.h>

/*enum xdp_action {
	XDP_ABORTED = 0,
	XDP_DROP,
	XDP_PASS,
	XDP_TX,
	XDP_REDIRECT,
};*/

//static long (* const bpf_trace_printk)(const char *fmt, __u32 fmt_size, ...) = (void *) 6;

#undef bpf_printk
#define bpf_printk(fmt, ...)                           \
{                                                      \
        char ____fmt[] = fmt;                           \
        bpf_trace_printk(____fmt, sizeof(____fmt),      \
                         ##__VA_ARGS__);                \
}

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


