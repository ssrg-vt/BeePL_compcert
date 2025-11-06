fun main () : int32, [] {
    let x : int32 = 2 in 
    let y : int32 = 4 in
    let r : int32* = ref 1 in  
    let _ : unit = for (x, y, Up, r := (!r + 1)) in 
    !r
}