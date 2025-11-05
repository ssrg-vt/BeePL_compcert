(* Dear kernel, whenever anyone calls execve(), 
   please run this little BeePL program that prints Hello from BeePL! *)
(* sudo bpftool prog load BeePL_bpf_hello.o /sys/fs/bpf/hello autoattach
   sudo bpftool prog tracelog
   sudo cat /sys/kernel/debug/tracing/trace_pipe *)

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
fun tick_prog (struct trace_event_raw_sys_enter* p) : int32, [] {
    let r : int32 = bpf_printk("Hello from BeePL!", 18) in 0
}

