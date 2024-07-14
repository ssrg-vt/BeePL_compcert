#include <linux/types.h>
#include <asm/types.h>
#include <inttypes.h>
#include <stdint.h>
//#include <linux/bpf.h>
//#include <bpf/bpf_helpers.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf/bpf_helpers.h>

#undef bpf_printk
#define bpf_printk(fmt, ...)                           \
{                                                      \
        char ____fmt[] = fmt;                           \
        bpf_trace_printk(____fmt, sizeof(____fmt),      \
                         ##__VA_ARGS__);                \
}

#undef SEC
#define SEC(A) __attribute__ ((section(A),used))

char LICENSE[] SEC("license") = "Dual BSD/GPL";

int my_pid = 0;

SEC("tp/syscalls/sys_enter_write")
int handle_tp(void *ctx)
{
	int pid = bpf_get_current_pid_tgid() >> 32;

	if (pid != my_pid)
		return 0;

	bpf_printk("BPF triggered from PID %d.\n", pid);

	return 0;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/minimal/minimal.s ebpf/test/minimal/minimal.c 

