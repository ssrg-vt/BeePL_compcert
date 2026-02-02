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

(* The mutable global variable is not allowed in eBPF.
   Mutation should only come through eBPF maps *)
let counter : int32* = ref 0

(* This program faces verifier error because mutatable global variables
   are not allowed in eBPF *)
#ebpf
#section xdp
fun xdp_prog (ostruct xdp_md* ctx) : int32, [] {
  let d : int32 = bpf_printk("Hello World %d", 15, counter) in
  let c : int32 = (!counter) + 1 in 
  2
}
