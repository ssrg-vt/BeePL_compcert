Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*  int add(int x, int y) {
 *    int r;
 *    r = x + y;
 *    return r;
 *  }
 *     
 *  int main(void) {
 *    int a = 1;
 *    int b = 2;
 *    int c = add(a, b);
 *    return c;
 *  } 
 *
 *)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _add : ident := $"add".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_a, "a") :: 
                                                      (_b, "b") :: 
                                                      (_c, "c") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") ::
                                                      (_add, "add") :: 
                                                      (_main, "main") :: nil).

Definition f_add : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_y, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_vars := ((_r, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_r) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Prim (Bop Cop.Oadd) 
                                                      (Var _x (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                       Var _y (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Var _r (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

Definition f_app_add : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_a, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_b, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_c, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_a) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Bind 
                                                   (_b) 
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Bind 
                                                      (_c) 
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                      (App (Var _add (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) ::
                                                                             Ptype (BeeTypes.Tint I32 Signed dattr) :: nil) (* type signature *)
                                                                            (Divergence :: nil) (* effect, should be NONE*)
                                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                                           (Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                            Var _b (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                           (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Var _c (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_add, AST.Gfun(BeePL.Internal (f_add))) :: 
      (_main, AST.Gfun(BeePL.Internal (f_app_add))) :: nil.

Definition public_idents : list ident := (_main :: _add :: nil).