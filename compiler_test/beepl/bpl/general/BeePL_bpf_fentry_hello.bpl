(* 
// file: hello_fentry.bpf.c
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

SEC("fentry/do_sys_open")
int BPF_PROG(hello_fentry)
{
    bpf_printk("Hello from fentry!\\n");
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
#section fentry/do_sys_open
fun hello_fentry (struct pt_regs* ctx) : int32, [] {
  let _ : int32 = bpf_printk("Hello from fentry!", 18) in
  0
}
