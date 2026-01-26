fun fact (int32 n) : int32, [] {
  if (n <= 1) then 1 else n * fact(n-1)
}

fun main () : int32, [] {
  let res : int32 = fact(5) in
  res
}
