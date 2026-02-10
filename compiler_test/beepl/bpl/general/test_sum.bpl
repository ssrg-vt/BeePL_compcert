fun iterative_add(int32 n) : int32, [] {
    let r : int32* = ref 0 in
    let i : int32 = 1 in

    let _ : unit = for(i, n, Up, r := (!r + i)) in 
    !r
}

fun main() : int32, [] {
    let n : int32 = 5 in
    let sum : int32 = iterative_add(n) in
    sum
}
(* Runs but gives wrong output *) 
