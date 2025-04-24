Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     option_t r;
     r = None;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_option1 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) :: nil);
                                   fn_body := (Prim Massgn ((Var _r (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))) :: 
                                                            (Enone (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))) :: nil) 
                                               (Ptype Tunit))|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_option1))) :: nil.

Definition public_idents : list ident := (_main :: nil).


Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.
