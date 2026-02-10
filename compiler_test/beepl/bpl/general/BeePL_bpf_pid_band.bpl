(*
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

char LICENSE[] SEC("license") = "GPL";

SEC("tracepoint/syscalls/sys_enter_execve")
int tp_execve_pid_band(struct trace_event_raw_sys_enter *ctx)
{
    __u64 id  = bpf_get_current_pid_tgid();
    __u32 pid = id >> 32;
    __u32 band = pid % 3;

    if (band == 0) {
        bpf_printk("execve: pid band 0\n");
    } else if (band == 1) {
        bpf_printk("execve: pid band 1\n");
    } else {
        bpf_printk("execve: pid band 2\n");
    }

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
#section raw_tracepoint/sys_enter
fun handle_execve (struct trace_event_raw_sys_enter* p) : int32, [] {
  (* get pid *)
  let pid_tgid : ulong  = bpf_get_current_pid_tgid() in
  let pid_ul   : ulong  = pid_tgid >> (ulong)32 in
  let pid      : uint32 = (uint32) pid_ul in

  (* band = pid % 3 *)
  let band : uint32 = pid % (uint32)3 in

  if (band == (uint32)0) then
    let _ : int32 = bpf_printk("execve: pid band 0\n", 20) in
    0
  else if (band == (uint32)1) then
    let _ : int32 = bpf_printk("execve: pid band 1\n", 20) in
    0
  else
    let _ : int32 = bpf_printk("execve: pid band 2\n", 20) in
    0
}
