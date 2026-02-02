fun main () : int32, [] {
  let a : int32[4] = { 1, 2, 3, 4 } in
  let a2 : int32[4] = { a[0], 99, a[2], a[3] } in
  a2[1]
}
