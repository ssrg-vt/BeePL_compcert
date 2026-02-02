struct bpf_map {
  map_type    : int32,   
  max_entries : int32,
  key_size    : int32,
  value_size  : int32,
  flags       : int32
}

#section .maps
let counter_table : struct bpf_map =
  (struct bpf_map (map_type, max_entries, key_size, value_size, flags)
    (1,              
     5000000,        
     8,              
     8,              
     0))             

#section license
let _license : int8* = "GPL\0"

#ebpf
#section ksyscall/execve
fun hello (int8* ctx) : int32, [] {
    let d : int32 = bpf_printk("Hello!", 7) in 2
}
 
