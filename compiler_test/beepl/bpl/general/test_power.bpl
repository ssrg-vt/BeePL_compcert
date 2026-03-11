fun pow (int32 base, int32 exp) : int32, [] {
  let result : int32* = ref 1 in  
  let i : int32 = 1 in
  let _ : unit = for(i, exp, Up, result := (!result * base)) in
  !result
  
}

fun main () : int32, [] {
  let x : int32 = 2 in
  let y : int32 = 5 in
  let z : int32 = pow(x, y) in 
  z

}
