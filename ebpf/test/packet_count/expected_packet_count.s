// https://github.com/swarnpriya/eBPF_notes/blob/main/eBPF_Koka/packet_count/packet_count_eBPF.md

packet_count.bpf.o: file format elf64-bpf                            // Gives the information that .o is a 64-bit ELF with ebpf code

Disassembly of section xdp:                                          // Diassembly of the section xdp

0000000000000000 <packet_count>:                    
; bpf_printk("%d", counter);                                         // 9-13 corresponds to the bpf_printk
   0: 18 06 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r6 = 0 ll      // sets register r6 to 0 (r6 is callee saved register)
   2: 61 63 00 00 00 00 00 00 r3 = *(u32 *)(r6 + 0)                  // converts r6 as pointer and move it to r3
   3: 18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00 r1 = 0 ll      // sets register r1 to 0 (r1 is caller saved register)
   5: b7 02 00 00 03 00 00 00 r2 = 3                                 // sets regsiter r2 to 3 (r2 is caller saved register)
                                                                     // oxb7 is the opcode, 02 is the destination register and 03 is the imm
                                                                     // tells the kernel to set the register to 3 using the signature of bpf_insn
   6: 85 00 00 00 06 00 00 00 call 6                                 // 
; counter++;                                                         // 7-9 increments the counter 
   7: 61 61 00 00 00 00 00 00 r1 = *(u32 *)(r6 + 0)                  
   8: 07 01 00 00 01 00 00 00 r1 += 1
   9: 63 16 00 00 00 00 00 00 *(u32 *)(r6 + 0) = r1
; return XDP_PASS;                                                 // return 
  10: b7 00 00 00 02 00 00 00 r0 = 2                               // r0 contains 2 as XDP_PASS is 2 in enum type XDP_ACTION
  11: 95 00 00 00 00 00 00 00 exit      


/* 

#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

int counter = 0;

SEC("xdp")
int packet_count(void *ctx) {
    bpf_printk("%d", counter);
    counter++;
    return XDP_PASS;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL"; 

*/

/*
// 64 bits (8 bytes) long instruction but sometime can extend to 16 bytes.
struct bpf_insn { __u8 code;
        __u8 dst_reg:4;
        __u8 src_reg:4;
        __s16 off;
        __s32 imm;
};*/