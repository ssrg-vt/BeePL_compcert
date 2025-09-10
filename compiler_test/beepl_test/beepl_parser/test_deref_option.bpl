(* The program should not typecheck as we try to deref an option type *)
fun main (oint32* u) : int32, [] {
  !u + 2
}