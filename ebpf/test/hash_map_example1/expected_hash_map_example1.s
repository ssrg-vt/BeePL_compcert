hash_map_example.bpf.o: file format elf64-bpf

Disassembly of section ksyscall/execve:

0000000000000000 <hello>:
;     uid = bpf_get_current_uid_gid() & 0xFFFFFFFF;   //returns a 64 bits integer containing the current GID and UID
       0:       85 00 00 00 0f 00 00 00 call 15
       1:       67 00 00 00 20 00 00 00 r0 <<= 32
       2:       77 00 00 00 20 00 00 00 r0 >>= 32
       3:       7b 0a f8 ff 00 00 00 00 *(u64 *)(r10 - 8) = r0
       4:       bf a2 00 00 00 00 00 00 r2 = r10
       5:       07 02 00 00 f8 ff ff ff r2 += -8
;     p = bpf_map_lookup_elem(&counter_table, (&uid)); //returns a pointer to the corresponding value in the hash table 
       6:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
       8:       85 00 00 00 01 00 00 00 call 1
       9:       b7 01 00 00 01 00 00 00 r1 = 1
;     if (p!= 0) {
      10:       15 00 02 00 00 00 00 00 if r0 == 0 goto +2 <LBB0_2>
;         counter = *p;
      11:       79 01 00 00 00 00 00 00 r1 = *(u64 *)(r0 + 0)
;     }
      12:       07 01 00 00 01 00 00 00 r1 += 1

0000000000000068 <LBB0_2>:
;     counter++;
      13:       7b 1a f0 ff 00 00 00 00 *(u64 *)(r10 - 16) = r1
      14:       bf a2 00 00 00 00 00 00 r2 = r10
      15:       07 02 00 00 f8 ff ff ff r2 += -8
      16:       bf a3 00 00 00 00 00 00 r3 = r10
      17:       07 03 00 00 f0 ff ff ff r3 += -16
;     bpf_map_update_elem(&counter_table, &uid, &counter, 0);
      18:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
      20:       b7 04 00 00 00 00 00 00 r4 = 0
      21:       85 00 00 00 02 00 00 00 call 2
;     return 0;
      22:       b7 00 00 00 00 00 00 00 r0 = 0
      23:       95 00 00 00 00 00 00 00 exit

/* 

#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <stdint.h>
#include <stdlib.h>
#include <memory.h>

// How many times each different user has run programs.

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 5000000);
    __type(key, uint64_t);
    __type(value, uint64_t);
} counter_table SEC(".maps");

SEC("ksyscall/execve")

int hello(void *ctx) {
    uint64_t uid;
    uint64_t counter = 0;
    uint64_t *p;
    
    uid = bpf_get_current_uid_gid() & 0xFFFFFFFF;   //returns a 64 bits integer containing the current GID and UID
                                                    //gets the user id that is running the process that trigegered this krpobe event. 
                                                    //user-id is held in lowest 32 bits of the 64-bit value that gets returned. (top 32 holds the group id)
    p = bpf_map_lookup_elem(&counter_table, (&uid)); //returns a pointer to the corresponding value in the hash table 
    if (p!= 0) {
        counter = *p;
    }

    counter++;
    bpf_map_update_elem(&counter_table, &uid, &counter, 0);
    return 0;
}

*/