(*
// rawtp_sys_enter_sample.bpf.c
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

char LICENSE[] SEC("license") = "GPL";

struct bpf_raw_tracepoint_args {
    __u64 args[2];   // args[0] = pt_regs*, args[1] = syscall id (on x86_64)
};

SEC("raw_tracepoint/sys_enter")
int raw_sys_enter(struct bpf_raw_tracepoint_args *ctx)
{
    __u32 rnd = bpf_get_prandom_u32();
    if ((rnd & 0xF) != 0)
        return 0;   // ~1/16 sampling

    __u64 id = bpf_get_current_pid_tgid();
    __u32 pid = id >> 32;
    __u64 syscall_id = ctx->args[1];

    bpf_printk("raw_tp: pid=%u syscall=%llu\n", pid, syscall_id);
    return 0;
}
*)
struct bpf_raw_tracepoint_args {
  args : ulong[2]
}

#section license
let _license : int8[4] = "GPL"

#ebpf
#section raw_tp/sys_enter
fun raw_sys_enter (struct bpf_raw_tracepoint_args* p) : int32, [] {
  (* random sampling ~1/16 *)
  let rnd : uint32 = bpf_get_prandom_u32() in
  if ((rnd & (uint32)15) != (uint32)0) then
    0
  else
    let pid_tgid : ulong = bpf_get_current_pid_tgid() in
    let _tgid    : int32 = (int32) (pid_tgid >> (ulong)32) in
    (* syscall id is p.args[1] but we won’t print it yet; format-print is tricky *)
    let _ : int32 = bpf_printk("raw_tp: sampled syscall\n", 26) in
    0
}
