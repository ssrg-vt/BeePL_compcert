fun main () : int32, [] {
    let x : int32 = 5 in 
    let y : int32 = 2 in
    let r : int32* = ref 10 in  
    let _ : unit = for (x, y, Down, r := (!r + 1)) in 
    !r
}