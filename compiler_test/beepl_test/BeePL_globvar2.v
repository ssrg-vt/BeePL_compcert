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
Definition _counter_table : ident := $"counter_table".
Definition _main : ident := $"main".

Definition  ident_to_string : list (ident * string) := ((_counter_table, "counter_table")  ::
                                                        (_main, "main") :: nil).

Definition v_counter_table:= {|
  gvar_info := Maptype _counter_table (Int.repr 1) 5000000 trlongu trlongu;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {| fn_return := tint32s;
                          fn_effect := nil;
                          fn_callconv := cc_default;
                          fn_args := nil;
                          fn_vars := nil;
                          fn_body := (cint (Int.repr 0) tint32s)        
                          |}.


Definition bcomposites : list bcomposite_definition :=
nil.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := ((_counter_table, Gvar v_counter_table) :: (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil).

Definition public_idents : list ident := (_main :: _counter_table :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

