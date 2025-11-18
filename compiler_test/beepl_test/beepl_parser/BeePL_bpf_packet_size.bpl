struct xdp_md {
  _data             : uint32,
  _data_end         : uint32,
  _data_meta        : uint32,
  _ingress_ifindex  : uint32,
  _rx_queue_index   : uint32,
  _egress_ifindex   : uint32
}

#section license
let _license : int8[4] = "GPL"

#ebpf
#section xdp
fun xdp_prog (struct xdp_md* ctx) : int32, [] {
let ds : uint32  = ctx._data in  
(* let de : uint32 = ctx._data_end in 
let pz : uint32 = de - ds in *)
if (ds > (uint32)70) 
then let r : int32 = bpf_printk ("Hello!", 6) in 
     2
else 1
}

