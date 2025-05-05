Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*// Global variable
int x = 5;

// Function that modifies the global variable
void update() {
    x = x + 1;
}

int main(void) {
    update();
    return x;
}*)

(*Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _val : ident := $"val".
Definition _temp : ident := $"temp".
Definition _update : ident := $"update".
Definition _main : ident := $"main".

Definition  ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                        (_val, "val") ::
                                                        (_update, "update") ::
                                                        (_main, "main") :: nil).

Definition v_x := {|
  gvar_info := trint32u;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_update := {| fn_return := tunit;
                          fn_effect := Read mem_ident :: Write mem_ident :: nil;
                          fn_callconv := cc_default;
                          fn_args := nil;
                          fn_vars := nil;
                          fn_body :=
                           Prim Massgn (Var _x trint32u ::
                                        (Prim (Bop Cop.Oadd) 
                                           (Prim Deref (Var _x trint32u :: nil) tint32u ::
                                            cint (Int.repr 1) tint32u :: nil) tint32u) :: nil) tunit
                                   
                          |}.

Definition v_val := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 5) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {| fn_return := tint32u;
                          fn_effect := Read mem_ident :: Write mem_ident :: nil;
                          fn_callconv := cc_default;
                          fn_args := nil;
                          fn_vars := nil;
                          fn_body :=
                             Bind _x trint32u (Prim Ref (Var _val tint32u :: nil) trint32u)
                               (Bind _temp tunit
                                (App (Var _update (tfun nil nil tint32u)) nil tunit)
                           (Prim Deref (Var _x trint32u :: nil) tint32u) tunit) tint32u
                                   
                          |}.

Definition bcomposites : list bcomposite_definition :=
nil.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := ((_x, Gvar v_x) :: (_update, AST.Gfun(BeePL.Internal (f_update))) :: 
       (_val, Gvar v_val) :: (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil).

Definition public_idents : list ident := (_main :: _update :: _x :: _val :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.
*)
