#ebpf
#section foo
fun main () : int32, [] {
  let x : int32 = 4 in 
  if true then x else 0
}

struct Point {
  x : int32,
  y : int32
}

