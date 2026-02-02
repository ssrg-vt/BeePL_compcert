fun main () : int32, [] {
  let u : int32* = ref 2 in   
  let _ : unit = u := 3 in 
  !u 
}