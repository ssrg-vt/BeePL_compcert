(*#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

// attach this to any tracepoint (e.g., sys_enter_execve) for demo
SEC("tracepoint/syscalls/sys_enter_execve")
int print_tick(void *ctx)
{
    bpf_printk("tick\n");
    return 0;
}

char LICENSE[] SEC("license") = "GPL";*)

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
let _license : int8* = "GPL"

#ebpf
#section tracepoint/syscalls/sys_enter_execve
fun tick_prog (ostruct trace_event_raw_sys_enter* p) : int32, [] {
    let r : int32 = bpf_printk("tick", 5) in 0
}
