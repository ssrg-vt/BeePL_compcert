fun rthen () : int32, [] {
    if true then 1 else 0
}

fun main() : int32, [] {
    let x : int32 = rthen() in x
}