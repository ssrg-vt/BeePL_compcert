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
fun xdp_prog (ostruct xdp_md* p) : int32, [] {
  let d : int32 = bpf_printk("Hello!", 7) in 2
}
