#include <linux/types.h>
#include <asm/types.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdint.h>
//#include <linux/bpf.h>
//#include <bpf/bpf_helpers.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf.h>
#include </home/swarnp/research/compcert_bpf/CompCert/ebpf/lib/bpf/bpf_helpers.h>

#undef bpf_printk
#define bpf_printk(fmt, ...)                           \
{                                                      \
        char ____fmt[] = fmt;                           \
        bpf_trace_printk(____fmt, sizeof(____fmt),      \
                         ##__VA_ARGS__);                \
}

#undef SEC
#define SEC(A) __attribute__ ((section(A),used))

//typedef __uint64_t uint64_t;

// How many times each different user has run programs.

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 5000000);
    //__type(key, uint64_t);         // doesn't understand typeof FIXME
    //__type(value, uint64_t);       // doesn't understand typeof FIXME
} counter_table SEC(".maps");

SEC("ksyscall/execve")

int hello(void *ctx) {
    uint64_t uid;
    uint64_t counter = 0;
    uint64_t *p;
    uint64_t mask = 0xFFFFFFFF;
    uid = bpf_get_current_uid_gid() & mask;   //returns a 64 bits integer containing the current GID and UID
                                                    //gets the user id that is running the process that trigegered this krpobe event. 
                                                    //user-id is held in lowest 32 bits of the 64-bit value that gets returned. (top 32 holds the group id)
    p = (uint64_t *)bpf_map_lookup_elem(&counter_table, (&uid)); //returns a pointer to the corresponding value in the hash table 
    if (p!= 0) {
        counter = *p;
    }

    counter++;
    bpf_map_update_elem(&counter_table, &uid, &counter, 0);
    return 0;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/hash_map_example1/hash_map_example1.s ebpf/test/hash_map_example1/hash_map_example1.c 

