(* Low byte of -1 (0xFFFFFFFF) is 0xFF → $? = 255. *)
fun main () : int32, [] {
  let u : uint32 = (uint32) 4294967295L in   (* UINT32_MAX *)
  let s : int32  = (int32) u in              (* becomes -1 *)
  s
}