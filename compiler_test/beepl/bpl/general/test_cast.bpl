(* returns 44 : 300 doesn’t fit in 8 bits, so it wraps to 300 mod 256 = 44.*)

fun main () : int32, [] {
  let x : int32 = 300 in
  let y : int8  = (int8) x in
  (int32) y            
}