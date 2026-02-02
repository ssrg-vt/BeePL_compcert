(* 
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>

/// @ifindex 1
/// @flags 0
/// @xdpopts {"old_prog_fd":0}
SEC("xdp")
int xdp_pass(struct xdp_md* ctx) {
    void_star data = (void_star)(long)ctx->data;
    void_star data_end = (void_star)(long)ctx->data_end;
    int pkt_sz = data_end - data;

    bpf_printk("packet size is %d", pkt_sz);
    return XDP_PASS;
}

char __license[] SEC("license") = "GPL"; *)

struct xdp_md {
  _data             : uint32,
  _data_end         : uint32,
  _data_meta        : uint32,
  _ingress_ifindex  : uint32,
  _rx_queue_index   : uint32,
  _egress_ifindex   : uint32
}

#section license
let _license : int8* = "GPL" 

#ebpf
#section xdp
fun xdp_pkt_size (ostruct xdp_md* ctx) : int32, [] {
  match ctx with 
  | some r -> let ds : uint32 = (!r)._data in 
              let de : uint32 = (!r)._data_end in 
              let pkt_size : uint32 = de - ds in 
              let re : int32 = bpf_printk("packet size is %d",18, pkt_size) in 2
  | none -> (int32) 0
}

