(*#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
    // Helper returns: (u64)(pid | (tgid << 32))
    u64 pid_tgid = bpf_get_current_pid_tgid();

    // Extract individual fields
    u32 pid = pid_tgid & 0xFFFFFFFF;
    u32 tgid = pid_tgid >> 32;

    bpf_printk("PID: %d, TGID: %d\n", pid, tgid);

    return XDP_PASS;
} *)

struct xdp_md {
    _data : uint32,
    _data_end : uint32,
    _data_meta : uint32,
    _ingress_ifindex : uint32,
    _rx_queue_index : uint32,
    _egress_ifindex : uint32
}

#section license
let _license : int8[4] = "GPL\0"

#ebpf
#section xdp
fun xdp_prog (struct xdp_md* p) : int32, [] {
    let pid_tgid : ulong = bpf_get_current_pid_tgid() in 
    let pid : int32 = (int32) (pid_tgid & (ulong)4294967295) in 
    let tgid : int32 = (int32) (pid_tgid >> (ulong)32) in 
    let r : int32 = bpf_printk("PID: %d, TGID: %d\n", pid, tgid) in 
    2
}
	
