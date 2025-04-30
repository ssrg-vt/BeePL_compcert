Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     unsigned int x = 1;
     unsigned int y = 2;
     unsigned int r = x + y;
     return r;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_add : BeePL.function := {| 
                                   fn_sec := Some "xdp";
                                   fn_return := (tint32s);
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tint32s) :: 
                                               (_y, tint32s) :: 
                                               (_r, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (tint32s)
                                                (Const (ConsInt (Int.repr 1)) (tint32s))
                                                (Bind 
                                                   (_y) 
                                                   (tint32s)
                                                   (Const (ConsInt (Int.repr 2)) (tint32s))
                                                   (Bind 
                                                      (_r) 
                                                      (tint32s)
                                                      (Prim (Bop Cop.Oadd) 
                                                            (Var _x (tint32s) :: 
                                                             Var _y (tint32s) :: nil)
                                                            (tint32s))
                                                      (Var _r (tint32s))
                                                      (tint32s))
                                                   (tint32s))
                                                (tint32s); 
                                   is_ebpf := false|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_add))) :: nil.

Definition public_idents : list ident := (_main :: nil).
