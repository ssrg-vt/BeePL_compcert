struct xdp_md {
    _data : uint32,
    _data_end : uint32,
    _data_meta : uint32,
    _ingress_ifindex : uint32,
    _rx_queue_index : uint32,
    _egress_ifindex : uint32
}

#ebpf
#section xdp
fun xdp_prog (struct xdp_md* p) : int32, [] {
    let x : int32 = 2 in x
}
	
