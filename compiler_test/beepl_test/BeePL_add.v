Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
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

(* attr_alignas is optional *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_add : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_y, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_r, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Bind 
                                                   (_y) 
                                                   (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Bind 
                                                      (_r) 
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                      (Prim (Bop Cop.Oadd) 
                                                            (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                                             Var _y (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Var _r (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr)) |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_add))) :: nil.

Definition public_idents : list ident := (_main :: nil).
