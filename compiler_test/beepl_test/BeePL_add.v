Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
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
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
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



(*Compute (type_check_program example1). *) (* Type checking works *)

(*Compute (type_check_expr empty_context empty_context f_add.(fn_body)).*)

