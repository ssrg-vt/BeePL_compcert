struct Point {
  x : int32,
  y : int32
}

#ebpf
#section foo 
fun add () : int32, [] {
  let x : int32 = 2 in 
  if true then x else 0
}
