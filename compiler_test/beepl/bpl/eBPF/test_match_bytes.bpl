(*struct xdp_md {
  _data             : uint32,
  _data_end         : uint32,
  _data_meta        : uint32,
  _ingress_ifindex  : uint32,
  _rx_queue_index   : uint32,
  _egress_ifindex   : uint32
}

struct bytes_t {
  bytes_start : uint8*,
  bytes_end : uint8*
}*)

struct _xdp_md_bee {
  _data_bee : bytes,
  _data_meta : uint32,
  _ingress_ifindex : uint32,
  _rx_queue_index : uint32,
  _egress_ifindex : uint32
}

struct ethhdr {
  h_dest : uint8,
  h_source : uint8,
  h_proto : uint16
}

#section license
let _license : int8[4] = "GPL\0" 

#ebpf
#section xdp
fun xdp_drop_prog (ostruct _xdp_md_bee* ctx) : int32, [] {
  (* Pattern-match the packet bytes as an ethhdr; fallback arm drops if too short *)
  match ctx._data_bee with
  | Pbytes eth : struct ethhdr [ h_proto : uint16 ] ->
      if (h_proto == htons((uint16) 34525))    (* 0x86DD (IPv6 ethertype) *)
      then 1                                   (* XDP_DROP *)
      else 2                                   (* XDP_PASS *)
  | Pbytes p : bytes [] ->
      1                                        (* drop if not enough bytes for ethhdr *)
}
