
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <stdio.h>

int main() {
    x = 0;
    for (int i = 1; i <= 5; i++) {
            x := !x + 1;
    }
   return !x;
}
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _t : ident := $"t".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_t, "t") ::
                                                      (_main, "main") :: nil).

Definition f_for : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := (Alloc mem_ident :: Read mem_ident :: Write mem_ident :: Read mem_ident :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, trint32s) ::
                                               (_t, tint32s) :: nil);
                                   fn_body := (Bind _x trint32s
                                                       (Prim Ref (cint (Int.repr 0) tint32s :: nil) trint32s)
                                                       (Bind _t tunit
                                                          (For
                                                             (cint (Int.repr 1) tint32s)
                                                             (cint (Int.repr 5) tint32s)
                                                             Up
                                                             (Prim Massgn 
                                                                     (Var _x trint32s ::
                                                                      (Prim (Bop Cop.Oadd) 
                                                                        (Prim Deref (Var _x trint32s :: nil) tint32s ::
                                                                         cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tunit) tunit)
                                                        (Prim Deref (Var _x trint32s :: nil)  tint32s) tint32s) tint32s);
                                   is_ebpf := false |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_for)), None) :: nil.

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

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_for.(fn_args)) f_for.(fn_vars)) empty_context f_for.(fn_body)).
Compute (type_check_program example1). *) (* Type checks *)
