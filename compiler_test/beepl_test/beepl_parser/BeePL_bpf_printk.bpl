(* 
#include <linux/bpf.h>
#include "bpf_helpers.h"

SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
    // Call a helper to print hello whenever a packet arrives
    bpf_printk("hello");

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

(*let _license : int8[4] = {71, 80, 76, 0} *)


#ebpf
#section xdp
fun xdp_prog (struct xdp_md* p) : int32, [] {
    let d : int32 = bpf_printk("Hello!", 6) in 2
}
	
