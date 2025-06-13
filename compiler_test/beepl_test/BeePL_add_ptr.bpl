func add (x : int32s) (y : int32s) : int32s =
  int32s.add x y

func main () : int32s =
  let (a : int32s) = 1 in
  let (fp : int32s -> int32s -> int32s) = add in
  let (r : int32s) = fp a a in
  r

let () = main ()
