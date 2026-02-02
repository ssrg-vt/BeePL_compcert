struct Point {
  x : int32,
  y : int32
}

fun main () : int32, [] {
  let p : struct Point* = ref (struct Point (x, y) (1, 2)) in
  (!p).y
}