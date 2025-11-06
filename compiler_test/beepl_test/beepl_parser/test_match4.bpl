fun main () : int32, [] {
  let p  : int32*   = ref 4 in
  let u  : oint32*  = some p in
  match u with 
  | some v -> !v
  | none -> 0
}