Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*  int main(void) {
 *    int x;
 *    x = 1;
 *    if (x < 3) {
 *      return 0;
 *    } else {
 *      return 2;
 *    }
 *  }
 * 
 *)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_conditional_1 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Cond (Prim (Bop Cop.Olt) 
                                                            (Var _x (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                             Const (ConsInt (Int.repr 3)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Const (ConsInt (Int.repr 0)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

(*  int main(void) {
 *    int x;
 *    int y;
 *    x = 1;
 *    y = x < 3 ? 0 : 2;
 *    return y;
 *  } 
 *
 *)

Definition f_conditional_2 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) ::
                                               (_y, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Bind 
                                                      (_y) 
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                      (Cond (Prim (Bop Cop.Olt) 
                                                                  (Var _x (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                                   Const (ConsInt (Int.repr 3)) (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                                  (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                            (Const (ConsInt (Int.repr 0)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                            (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Var _y (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_conditional_1))) :: nil.

Definition public_idents : list ident := (_main :: nil).
