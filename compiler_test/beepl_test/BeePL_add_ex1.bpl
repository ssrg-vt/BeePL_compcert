func f_add () : int32u =
  let (_x : int32u) = 40 in
  let (_y : int32u) = 40 in
  let (_r : int32u) = int32u.add _x _y in
  _r

func _main () : int32u = f_add ()

let () = _main ()
