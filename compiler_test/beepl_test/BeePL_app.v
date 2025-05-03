Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
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
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, tint32s) :: 
                                               (_y, tint32s) :: nil);
                                   fn_vars := ((_r, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_r) tint32s
                                                (Prim (Bop Cop.Oadd) 
                                                      (Var _x tint32s :: 
                                                       Var _y tint32s :: nil) tint32s)
                                                (Var _r tint32s) tint32s |}.

(*
 *  int add(int x, int *y) {
 *    int r;
 *    r = x + *y;
 *    return r;
 *  }
 *     
 *)
Definition f_add_with_one_ref : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, tint32s) :: 
                                               (_y, trint32s) :: nil);
                                   fn_vars := ((_r, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_r) tint32s
                                                (Prim (Bop Cop.Oadd) 
                                                      (Var _x tint32s :: 
                                                       Prim (Deref) 
                                                            (Var _y trint32s :: nil) tint32s :: nil) tint32s)
                                                (Var _r tint32s) tint32s |}.

(*
 *  int add(int *x, int *y) {
 *    int r;
 *    r = *x + *y;
 *    return r;
 *  }
 *     
 *)
Definition f_add_with_two_ref : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, trint32s) :: 
                                               (_y, trint32s):: nil);
                                   fn_vars := ((_r, trint32s) :: nil);
                                   fn_body := Bind 
                                                (_r) tint32s
                                                (Prim (Bop Cop.Oadd) 
                                                      (Prim (Deref) 
                                                            (Var _x trint32s :: nil) tint32s :: 
                                                        Prim (Deref) 
                                                             (Var _y trint32s :: nil) tint32s :: nil) tint32s)
                                                (Var _r tint32s) tint32s |}.

(*  int main(void) {
 *    int a = 1;
 *    int b = add(a, 2); // <- should be ref(2)
 *    return b;
 * } 
 *
 *)
Definition f_main : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_a, tint32s) :: 
                                               (_b, tint32s) :: nil);
                                   fn_body := 
                                              Bind 
                                                   (_a) tint32s 
                                                   (cint (Int.repr 1) tint32s)
                                                   (Bind 
                                                      (_b) tint32s
                                                      (App (Var _add (tfun (tint32s :: tint32s :: nil) (* type signature *)
                                                                            nil (* effect *)
                                                                            tint32s)) (* return type *)
                                                           (Var _a tint32s :: 
                                                            Var _a tint32s :: nil) tint32s)
                                                      (Bind 
                                                          (_b) tint32s
                                                          (App (Var _add_with_one_ref (tfun (tint32s :: trint32s :: nil) (* type signature *)
                                                                                       nil (* effect *)
                                                                                       tint32s)) (* return type *)
                                                               (Var _a tint32s :: 
                                                                Prim (Ref) 
                                                                     (cint (Int.repr 1) tint32s :: nil) trint32s :: nil) tint32s)
                                                          (Bind 
                                                             (_b) tint32s
                                                             (App (Var _add_with_two_ref (tfun (trint32s :: trint32s :: nil) (* type signature *)
                                                                                           nil (* effect *)
                                                                                          tint32s)) (* return type *)
                                                                  (Prim (Ref) 
                                                                        (cint (Int.repr 5) tint32s :: nil) trint32s ::
                                                                   Prim (Ref) 
                                                                        (cint (Int.repr 173) tint32s :: nil) trint32s :: nil) tint32s)
                                                             (Var _b tint32s) tint32s) tint32s) tint32s) tint32s |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_add, AST.Gfun(BeePL.Internal (f_add))) ::
      (_add_with_one_ref, AST.Gfun(BeePL.Internal (f_add_with_one_ref))) ::
      (_add_with_two_ref, AST.Gfun(BeePL.Internal (f_add_with_two_ref))) ::
      (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil.

Definition public_idents : list ident := (_main :: _add :: nil).


Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_program example1).*) (* Type checks *)
