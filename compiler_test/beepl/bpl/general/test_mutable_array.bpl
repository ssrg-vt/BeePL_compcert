fun main () : int32, [] {
  let ma : int32*[3] = { ref 10, ref 20, ref 30 } in

  let x : unit = ma[0] := 100 in

  !ma[0]
}
