Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
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

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_conditional_1 : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_x) tint32s
                                                (cint (Int.repr 1) tint32s)
                                                (Cond (Prim (Bop Cop.Olt) 
                                                            (Var _x tint32s :: 
                                                             cint (Int.repr 3) tint32s :: nil)
                                                             tbbool)
                                                      (cint (Int.repr 0) tint32s) 
                                                      (cint (Int.repr 2) tint32s) tint32s) tint32s |}.

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
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tint32s) ::
                                               (_y, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_x) tint32s
                                                (cint (Int.repr 1) tint32s) 
                                                (Bind 
                                                      (_y) tint32s
                                                      (Cond (Prim (Bop Cop.Olt) 
                                                                  (Var _x tint32s :: 
                                                                   cint (Int.repr 3) tint32s :: nil)
                                                                  tbbool)
                                                            (cint (Int.repr 0) tint32s)
                                                            (cint (Int.repr 2) tint32s) tint32s)
                                                      (Var _y tint32s) tint32s) tint32s |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_conditional_1))) :: nil.

Definition public_idents : list ident := (_main :: nil).

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

Compute (type_check_program example1).*)  (* Type Checks *)

