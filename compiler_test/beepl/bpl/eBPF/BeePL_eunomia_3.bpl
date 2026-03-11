(*#include "vmlinux.h"
#include <bpf/bpf_helpers.h>
#include <bpf/bpf_tracing.h>

char LICENSE[] SEC("license") = "Dual BSD/GPL";

SEC("fentry/do_unlinkat")
int BPF_PROG(do_unlinkat, int dfd, struct filename *name)
{
    pid_t pid;

    pid = bpf_get_current_pid_tgid() >> 32;
    bpf_printk("fentry: pid = %d, filename = %s\n", pid, name->name);
    return 0;
}

SEC("fexit/do_unlinkat")
int BPF_PROG(do_unlinkat_exit, int dfd, struct filename *name, long ret)
{
    pid_t pid;

    pid = bpf_get_current_pid_tgid() >> 32;
    bpf_printk("fexit: pid = %d, filename = %s, ret = %ld\n", pid, name->name, ret);
    return 0;
}
*)

struct filename {
  name : int8*
}

#section license
let _license : int8* = "Dual BSD/GPL"

#ebpf

#section fentry/do_unlinkat
fun do_unlinkat (struct filename* name) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : int32 = (int32)(pid_tgid >> (ulong)32) in

  let filename : int8* = name.name in

  let o : int32 =
    bpf_printk("fentry: pid = %d, filename = %s\n", 34, pid, filename)
  in
  0
}

#section fexit/do_unlinkat
fun do_unlinkat_exit (struct filename* name) : int32, [] {
  let pid_tgid : ulong = bpf_get_current_pid_tgid() in
  let pid      : int32 = (int32)(pid_tgid >> (ulong)32) in

  let filename : int8* = name.name in

  let o : int32 =
    bpf_printk("fexit: pid = %d, filename = %s, ret = %ld\n", 45, pid, filename) in
  0
}

