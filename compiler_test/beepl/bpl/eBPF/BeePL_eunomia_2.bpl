(* #include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>
#include <bpf/bpf_core_read.h>

char LICENSE[] SEC("license") = "Dual BSD/GPL";

SEC("kprobe/do_unlinkat")
int BPF_KPROBE(do_unlinkat, int dfd, struct filename *name)
{
    pid_t pid;
    const char *filename;

    pid = bpf_get_current_pid_tgid() >> 32;
    filename = BPF_CORE_READ(name, name);
    bpf_printk("KPROBE ENTRY pid = %d, filename = %s\n", pid, filename);
    return 0;
}

SEC("kretprobe/do_unlinkat")
int BPF_KRETPROBE(do_unlinkat_exit, long ret)
{
    pid_t pid;

    pid = bpf_get_current_pid_tgid() >> 32;
    bpf_printk("KPROBE EXIT: pid = %d, ret = %ld\n", pid, ret);
    return 0;
} 
*)

struct filename {
  name : int8*
}

#section license
let _license : int8* = "Dual BSD/GPL"

#ebpf
#section kprobe/do_unlinkat
fun do_unlinkat (struct filename* fname) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : int32 = (int32)(pid_tgid >> (ulong)32) in


  let filename_ptr : int8* = fname.name in

  let i : int32 =
    bpf_printk("KPROBE ENTRY pid = %d, filename = %s\n", 39, pid, filename_ptr)
  in
  0
}

#section kretprobe/do_unlinkat
fun do_unlinkat_exit (int32 ret) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : int32 = (int32)(pid_tgid >> (ulong)32) in

  let j : int32 =
    bpf_printk("KPROBE EXIT: pid = %d, ret = %ld\n", 35, pid, ret)
  in
  0
}
