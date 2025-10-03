(* 
#include <linux/bpf.h>
#include "bpf_helpers.h"

SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
    // Call a helper to get a pseudo-random number
    __u32 rand = bpf_get_prandom_u32();

    // Always pass the packet (simplest behavior)
    return XDP_PASS;
}

char _license[] SEC("license") = "GPL"; *)

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
    let rand : uint32 = bpf_get_prandom_u32() in 2
}
	
