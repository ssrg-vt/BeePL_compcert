#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("tp/syscalls/sys_enter_getcwd")
int test(void *ctx)
{
    volatile __u32 A = 3;    
    volatile __u32 B = 2;
    volatile __u32 zero = 0;    
    
    if (A > 10)
        return XDP_PASS;

    if (B > 10)
        return XDP_PASS;

    A = A * B;

    if (A == 11)
        A = A / zero;

    return XDP_PASS;
}

char LISENSE[] SEC("license") = "Dual BSD/GPL";
