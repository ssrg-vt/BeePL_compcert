Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*// Global variable
// Global variable
int x = 0;

int main() {
    x++;
    return !x;
}*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _r : ident := $"r".
Definition _val : ident := $"_val".
Definition _main : ident := $"main".

Definition  ident_to_string : list (ident * string) := ((_x, "x") :: (_r, "r") ::
                                                        (_main, "main") :: nil).

Definition v_val := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_x := {|
  gvar_info := trint32u;
  gvar_init := (Init_addrof _val Ptrofs.zero :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {| fn_return := tint32s;
                          fn_effect := Read mem_ident :: Write mem_ident :: nil;
                          fn_callconv := cc_default;
                          fn_args := nil;
                          fn_vars := (_r, tint32s) :: nil;
                          fn_body :=
                           Bind _r tint32s
                           (Prim Massgn (Var _x trint32s ::
                                        (Prim (Bop Cop.Oadd) 
                                           (Prim Deref (Var _x trint32s :: nil) tint32s ::
                                            cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tunit)
                           (Prim Deref (Var _x trint32s :: nil) tint32s) tint32s
                                   
                          |}.


Definition bcomposites : list bcomposite_definition :=
nil.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := ((_x, Gvar v_x) :: (_val, Gvar v_val) :: (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil).

Definition public_idents : list ident := (_main :: _x :: _val :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

