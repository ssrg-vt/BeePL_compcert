fun main (oint32* u) : int32, [] {
  match u with 
  | some r -> let _ : unit = r := 2 in !r
  | none -> 0
}

