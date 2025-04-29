
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <stdio.h>

int main() {
    x = ref 0;
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
                                   fn_return := (Ptype (Tint I32 Unsigned dattr));
                                   fn_effect := (Alloc mem_ident :: Read mem_ident :: Write mem_ident :: Read mem_ident :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr)) :: 
                                               (_t, Ptype (Tint I32 Unsigned dattr)) :: nil);
                                   fn_body := (Bind _x (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr)
                                                       (Prim Ref ((Const (ConsInt (Int.repr 0)) (Ptype (Tint I32 Unsigned dattr))) :: nil)
                                                             (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr))
                                                       (Bind _t (Ptype Tunit)
                                                          (For 
                                                             (Const (ConsInt (Int.repr 1)) (Ptype (Tint I32 Unsigned dattr)))
                                                             (Const (ConsInt (Int.repr 5)) (Ptype (Tint I32 Unsigned dattr)))
                                                             Up
                                                             (Prim Massgn (Var _x (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr) ::
                                                                     (Prim (Bop Cop.Oadd) 
                                                                        (Prim Deref (Var _x (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr) :: nil) 
                                                                             (Ptype (Tint I32 Unsigned dattr)) :: 
                                                                           Const (ConsInt (Int.repr 1)) (Ptype (Tint I32 Unsigned dattr)) :: nil)
                                                                        (Ptype (Tint I32 Unsigned dattr))) :: nil)
                                                            (Ptype Tunit))
                                                           (Ptype Tunit))
                                                        (Prim Deref (Var _x (Reftype mem_ident (Bprim (Tint I32 Unsigned dattr)) dattr) :: nil) 
                                                           (Ptype (Tint I32 Unsigned dattr)))
                                                     (Ptype (Tint I32 Unsigned dattr)))
                                               (Ptype (Tint I32 Unsigned dattr)))|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_for))) :: nil.

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
