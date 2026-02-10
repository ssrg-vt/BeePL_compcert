(*
// file: hello_kprobe.bpf.c
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

SEC("kprobe/do_sys_open")
int BPF_KPROBE(hello_kprobe)
{
    bpf_printk("Hello from kprobe!\\n");
    return 0;
}

char LICENSE[] SEC("license") = "GPL";

*)

struct pt_regs {
  regs : int32[21]
}

#section license
let _license : int8[4] = "GPL"

#ebpf
#section kprobe/__x64_sys_openat
fun hello_kprobe (struct pt_regs* ctx) : int32, [] {
  let _ : int32 = bpf_printk("Hello from kprobe!", 18) in
  0
}



