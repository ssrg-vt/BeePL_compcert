fun foo (int32 x) : int32, [] {
    if true then x else 0
}

fun main() : int32, [] {
    let x : int32 = foo(2) in x
}