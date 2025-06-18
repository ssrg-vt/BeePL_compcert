let (_r : int32s) = 0

func f_add () : int32s =
  let (_x : int32s ref) = ref 2 in
  let (_ : unit) = _x := int32s.add !_x 1 in
  !_x

func _main () : int32s = f_add ()

let () = _main ()
