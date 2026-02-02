(*
#define BPF_NO_GLOBAL_DATA
#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

typedef unsigned int u32;
typedef int pid_t;
const pid_t pid_filter = 0;

char LICENSE[] SEC("license") = "Dual BSD/GPL";

SEC("tp/syscalls/sys_enter_write")
int handle_tp(void *ctx)
{
 pid_t pid = bpf_get_current_pid_tgid() >> 32;
 if (pid_filter && pid != pid_filter)
  return 0;
 bpf_printk("BPF triggered sys_enter_write from PID %d.\n", pid);
 return 0;
} *)


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


(* This program defines a handle_tp function and attaches it to 
   the sys_enter_write tracepoint using the #section macro. 
   This means it gets executed every time the write system call is entered. 
   The function retrieves the process ID of the current process and prints 
   it to the kernel log using bpf_printk. *)
#section license
let _license : int8* = "GPL"

#ebpf
#section tp/syscalls/sys_enter_write
fun handle_tp (ostruct trace_event_raw_sys_enter* ctx) : int32, [] {
	let pid_tgid : ulong = bpf_get_current_pid_tgid() in 
  let pid : ulong = pid_tgid >> (ulong) 32 in 
	let rpid : uint32 =  (uint32) pid in 
	if (rpid == (uint32) 0) 
	then 0
	else let r : int32 = bpf_printk("BPF triggered sys_enter_write from PID %d.", 43, rpid) in 0
}

(* sudo bpftool prog load BeePL_eunomia_example1.o /sys/fs/bpf/tp_write autoattach *)