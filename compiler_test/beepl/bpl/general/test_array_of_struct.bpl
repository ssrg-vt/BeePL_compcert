struct Point {
  x : int32,
  y : int32
}

fun main () : int32, [] {
  let pts : struct Point[2] =
    { (struct Point (x, y) (1, 2)),
      (struct Point (x, y) (3, 4)) } in

  pts[1].x
}
