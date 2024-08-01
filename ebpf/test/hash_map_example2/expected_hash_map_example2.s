hash_map_example.bpf.o: file format elf64-bpf

Disassembly of section ksyscall/execve:

0000000000000000 <hello>:
;     uid = bpf_get_current_uid_gid() & 0xFFFFFFFF;   //returns a 64 bits integer containing the current GID and UID
       0:       85 00 00 00 0f 00 00 00 call 15
       1:       67 00 00 00 20 00 00 00 r0 <<= 32
       2:       77 00 00 00 20 00 00 00 r0 >>= 32
       3:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
       5:       7b 01 00 00 00 00 00 00 *(u64 *)(r1 + 0) = r0
;     p = bpf_map_lookup_elem(&counter_table, (&uid)); //returns a pointer to the corresponding value in the hash table 
       6:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
       8:       18 02 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r2 = 0 ll
      10:       85 00 00 00 01 00 00 00 call 1
      11:       b7 01 00 00 01 00 00 00 r1 = 1
;     if (p!= 0) {
      12:       15 00 02 00 00 00 00 00 if r0 == 0 goto +2 <LBB0_2>
;         counter = *p;
      13:       79 01 00 00 00 00 00 00 r1 = *(u64 *)(r0 + 0)
;     }
      14:       07 01 00 00 01 00 00 00 r1 += 1

0000000000000078 <LBB0_2>:
;     counter++;
      15:       7b 1a f8 ff 00 00 00 00 *(u64 *)(r10 - 8) = r1
      16:       bf a3 00 00 00 00 00 00 r3 = r10
      17:       07 03 00 00 f8 ff ff ff r3 += -8
;     bpf_map_update_elem(&counter_table, &uid, &counter, 0);
      18:       18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
      20:       18 02 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r2 = 0 ll
      22:       b7 04 00 00 00 00 00 00 r4 = 0
      23:       85 00 00 00 02 00 00 00 call 2
;     return 0;
      24:       b7 00 00 00 00 00 00 00 r0 = 0
      25:       95 00 00 00 00 00 00 00 exit