(* #include <vmlinux.h>
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

struct trace_entry {
    _type : uint32,
    _flags : uint32,
    _preempt_count : uint32,
    _pid : int32 
}

struct trace_event_raw_sys_enter {
    _ent : struct trace_entry,
    _id : ulong
}



#ebpf
#section tracepoint_syscalls_sys_enter_openat
fun tracepoint__syscalls__sys_enter_openat (struct trace_event_raw_sys_enter* p) : int32, [] {
    let pid_target : int32 = 0 in 
    let pid_tgid : ulong = bpf_get_current_pid_tgid() in 
    let pid : int32 = (int32) (pid_tgid & (ulong)4294967295) in 
    let tgid : int32 = (int32) (pid_tgid >> (ulong)32) in 

    let val1 : bool = pid_target != tgid in 
    
    (* let val2 : bool = pid_target in
    let val : bool = val1 & val2 in *)

    let r : int32 = bpf_printk("Process ID: %d enter sys openat\n", pid) in 
    if val1 then 1 else r
}


