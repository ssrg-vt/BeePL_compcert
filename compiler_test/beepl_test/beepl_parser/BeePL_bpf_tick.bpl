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

struct trace_event_raw_sys_enter {
  __unused__ : long,
  id : long,
  args : long[6]
}

#section license
let _license : int8[4] = "GPL\0"

#ebpf
#section tracepoint/syscalls/sys_enter_execve
fun tick_prog (struct trace_event_raw_sys_enter* p) : int32, [] {
    let r : int32 = bpf_printk("tick", 4) in 0
}