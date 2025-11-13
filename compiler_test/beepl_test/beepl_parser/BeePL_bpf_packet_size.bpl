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
fun xdp_prog (ostruct xdp_md* ctx) : int32, [] {
  match ctx with
  | some d -> let ds : uint32  = d._data in  
              let de : uint32 = d._data_end in 
	      let pz : uint32 = ds - de in 
              if (pz > (uint32)70) 
	      then bpf_printk ("The packet size is greater than 70", 35)
              else bpf_printk ("The packet size is smaller than 70", 35)
  | none -> bpf_printk ("No xdp context at the pointer", 29) 
}

