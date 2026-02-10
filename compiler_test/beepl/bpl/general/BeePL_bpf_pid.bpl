(*
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

char LICENSE[] SEC("license") = "GPL";

// tracepoint context type for sys_enter_* is usually trace_event_raw_sys_enter,
// but we don't use ctx at all here.
SEC("tracepoint/syscalls/sys_enter_execve")
int handle_execve(struct trace_event_raw_sys_enter *ctx)
{
    __u64 id = bpf_get_current_pid_tgid();
    __u32 pid = id >> 32;  // upper 32 bits

    bpf_printk("execve called by pid=%u\n", pid);
    return 0;
}
*)

struct trace_entry {
  type           : uint16,
  flags          : uint8,
  preempt_count  : uint8,
  pid            : int32
}

struct trace_event_raw_sys_enter {
  ent  : struct trace_entry,
  id   : long,
  args : ulong[6]
}

#section license
let _license : int8[4] = "GPL"

#ebpf
#section tracepoint/syscalls/sys_enter_execve
fun handle_execve (struct trace_event_raw_sys_enter* ctx) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : ulong = pid_tgid >> (ulong)32 in


  let _ : int32 = bpf_printk("execve called", 13) in
  0
}

