Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* option_t main() {
     option_t r;
     return r;
  }
*)

(* attr_alignas is optional *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_option1 : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) :: nil);
                                   fn_body := (Var _r (BeeTypes.Otype (Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))) |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_option1))) :: nil.

Definition public_idents : list ident := (_main :: nil).


Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_default :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.
