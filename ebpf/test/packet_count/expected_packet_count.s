// https://github.com/swarnpriya/eBPF_notes/blob/main/eBPF_Koka/packet_count/packet_count_eBPF.md

packet_count.bpf.o: file format elf64-bpf

Disassembly of section xdp:

0000000000000000 <packet_count>:
; bpf_printk("%d", counter);
   0: 18 06 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r6 = 0 ll
   2: 61 63 00 00 00 00 00 00 r3 = *(u32 *)(r6 + 0)
   3: 18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll
   5: b7 02 00 00 03 00 00 00 r2 = 3
   6: 85 00 00 00 06 00 00 00 call 6
; counter++;
   7: 61 61 00 00 00 00 00 00 r1 = *(u32 *)(r6 + 0)
   8: 07 01 00 00 01 00 00 00 r1 += 1
   9: 63 16 00 00 00 00 00 00 *(u32 *)(r6 + 0) = r1
; return XDP_PASS;
  10: b7 00 00 00 02 00 00 00 r0 = 2
  11: 95 00 00 00 00 00 00 00 exit      

