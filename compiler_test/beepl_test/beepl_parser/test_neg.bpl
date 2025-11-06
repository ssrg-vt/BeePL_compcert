(* Produces output 251: printing unsigned int 
   In Unix, the exit code is an 8-bit unsigned integer (0–255).*)
fun main() : int32, [] {
    let x : int32 = 5 in 
        let y : int32 = -x in 
        y
}