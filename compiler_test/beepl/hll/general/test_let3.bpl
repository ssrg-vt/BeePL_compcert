(* int x = 2;
{
  int x = 3;
  int y = x + x;  // uses inner x = 3 → y = 6
}                 // inner x,y go out of scope
y = x + 1;        // uses OUTER x = 2 → y = 3
return y;         // 3 *)

fun main () : int32, [] {
  let x1 : int32 = 2 in
  let y : int32 =
    (* inner block *)
    let x2 : int32 = 3 in
    x2 + x2               (* = 6 *)
  in
  let y1 : int32 = x1 + 1 in   (* x here is the OUTER one: 2 *)
  y1
}