(* 4000000000 doesn’t fit in signed 32-bit; 
   interpreting the same bits as int32 gives -294967296. *)
(* x : uint32 = 4000000000 → bits 0xEE6B2800
   y : int32 = (int32) x → same bits reinterpreted as signed → -294,967,296 (since 4000000000 - 2^32 = -294,967,296)
   Shell exit codes are only the low 8 bits (0–255) of the return value.
   Low byte of 0xEE6B2800 is 0x00, so the exit status is 0. *)
fun main () : int32, [] {
  let x : uint32 = (uint32) 4000000000L in
  let y : int32  = (int32) x in
  y                    
}