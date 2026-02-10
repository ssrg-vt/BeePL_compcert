(*#include <vmlinux.h>
#include <bpf/bpf_helpers.h>

/// @description "Process ID to trace"
const volatile int pid_target = 0;

SEC("tracepoint/syscalls/sys_enter_openat")
int tracepoint__syscalls__sys_enter_openat(struct trace_event_raw_sys_enter* ctx)
{
    u64 id = bpf_get_current_pid_tgid();
    u32 pid = id >> 32;

    if (pid_target && pid_target != pid)
        return false;

    // Use bpf_printk to print the process information
    bpf_printk("Process ID: %d enter sys openat\n", pid);
    return 0;
}

/// "Trace open family syscalls."
char LICENSE[] SEC("license") = "GPL";
*)

(* Minimal structs for the tracepoint context *)
struct trace_entry {
  type          : uint16,
  flags         : uint8,
  preempt_count : uint8,
  pid           : int32
}

struct trace_event_raw_sys_enter {
  ent  : struct trace_entry,
  id   : long,
  args : ulong[6]
}

(* @description "Process ID to trace" *)
let pid_target : int32 = 0

#section license
let _license : int8* = "GPL"

#ebpf
#section tracepoint/syscalls/sys_enter_openat
fun tracepoint__syscalls__sys_enter_openat (struct trace_event_raw_sys_enter* ctx) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : int32 = (int32)(pid_tgid >> (ulong)32) in

  (* print iff pid_filter == 0 OR pid == pid_filter *)
  let cond : int32 = pid_target * (pid_target - pid) in

  if (cond == 0)
  then
    let i : int32 =
      bpf_printk("BPF triggered sys_enter_write from PID %d.\n", 45, pid)
    in
    0
  else
    0
}
