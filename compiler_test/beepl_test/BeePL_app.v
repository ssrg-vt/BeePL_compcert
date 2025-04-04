Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _h : ident := $"h". (* supposed to represent heap for Reftype *)
Definition _add : ident := $"add".
Definition _add_with_one_ref : ident := $"add_with_one_ref".
Definition _add_with_two_ref : ident := $"add_with_two_ref".
Definition _main : ident := $"main".

Definition  ident_to_string : list (ident * string) := ((_a, "a") :: 
                                                        (_b, "b") :: 
                                                        (_c, "c") ::
                                                        (_x, "x") :: 
                                                        (_y, "y") :: 
                                                        (_r, "r") ::
                                                        (_add, "add") ::
                                                        (_add_with_one_ref, "add_with_one_ref") ::
                                                        (_add_with_two_ref, "add_with_two_ref") ::
                                                        (_main, "main") :: nil).
(*  int add(int x, int y) {
 *    int r;
 *    r = x + y;
 *    return r;
 *  }
 *     
 *)
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
(*
 *  int add(int x, int *y) {
 *    int r;
 *    r = x + *y;
 *    return r;
 *  }
 *     
 *)
Definition f_add_with_one_ref : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_y, BeeTypes.Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil);
                                   fn_vars := ((_r, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_r) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Prim (Bop Cop.Oadd) 
                                                      (Var _x (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                       Prim (Deref) 
                                                            (Var _y (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Var _r (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

(*
 *  int add(int x, int *y) {
 *    int r;
 *    r = x + *y;
 *    return r;
 *  }
 *     
 *)
Definition f_add_with_two_ref : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, BeeTypes.Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: 
                                               (_y, BeeTypes.Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil);
                                   fn_vars := ((_r, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := Bind 
                                                (_r) 
                                                (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                (Prim (Bop Cop.Oadd) 
                                                      (Prim (Deref) 
                                                            (Var _x (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                       Prim (Deref) 
                                                            (Var _y (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Var _r (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

(*  int main(void) {
 *    int a = 1;
 *    int b = add(a, 2); // <- should be ref(2)
 *    return b;
 * } 
 *
 *)
Definition f_main : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_a, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: 
                                               (_b, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) :: nil);
                                   fn_body := 
                                              Bind 
                                                   (_a) 
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                   (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Bind 
                                                      (_b) 
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                      (App (Var _add (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) :: Ptype (BeeTypes.Tint I32 Signed dattr) :: nil) (* type signature *)
                                                                            (nil) (* effect *)
                                                                            (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                                           (Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                            Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: nil)
                                                           (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Bind 
                                                          (_b) 
                                                          (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                          (App (Var _add_with_one_ref (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) :: Ptype (BeeTypes.Tint I32 Signed dattr) :: nil) (* type signature *)
                                                                                (nil) (* effect *)
                                                                                (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                                               (Var _a (Ptype (BeeTypes.Tint I32 Signed dattr)) :: 
                                                                Prim (Ref) 
                                                                     (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Ctypes.Signed dattr)) :: nil)
                                                                     (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                               (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                          (Bind 
                                                             (_b) 
                                                             (Ptype (BeeTypes.Tint I32 Signed dattr))
                                                             (App (Var _add_with_two_ref (Ftype (Ptype (BeeTypes.Tint I32 Signed dattr) :: Ptype (BeeTypes.Tint I32 Signed dattr) :: nil) (* type signature *)
                                                                                   (nil) (* effect *)
                                                                                   (Ptype (BeeTypes.Tint I32 Signed dattr)))) (* return type *)
                                                                  (Prim (Ref) 
                                                                        (Const (ConsInt (Int.repr 5)) (Ptype (BeeTypes.Tint I32 Ctypes.Signed dattr)) :: nil)
                                                                        (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: 
                                                                   Prim (Ref) 
                                                                        (Const (ConsInt (Int.repr 173)) (Ptype (BeeTypes.Tint I32 Ctypes.Signed dattr)) :: nil)
                                                                        (Reftype _h (Bprim (BeeTypes.Tint Ctypes.I32 Ctypes.Signed dattr)) dattr) :: nil)
                                                                  (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                             (Var _b (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                             (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                             (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                   (Ptype (BeeTypes.Tint I32 Signed dattr)) |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_add, AST.Gfun(BeePL.Internal (f_add))) ::
      (_add_with_one_ref, AST.Gfun(BeePL.Internal (f_add_with_one_ref))) ::
      (_add_with_two_ref, AST.Gfun(BeePL.Internal (f_add_with_two_ref))) ::
      (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil.

Definition public_idents : list ident := (_main :: _add :: nil).
