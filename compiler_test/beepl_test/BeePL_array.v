Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux BeePL_notations.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     unsigned int arr[2] = {1;2};
     return 0;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _arr : ident := $"arr".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_arr, "arr") :: (_r, "r") ::
                                                       (_main, "main") :: nil).

Definition f_array : BeePL.function := {| 
                                   fn_return := (Vtype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_arr, BeeTypes.Atype (Vtype (BeeTypes.Tint I32 Unsigned dattr)) 2 dattr) :: 
                                               (_r, Vtype (BeeTypes.Tint I32 Unsigned dattr)) :: nil);
                                   fn_body := Bind 
                                                (_r) (Vtype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Ainit _arr (BeeTypes.Atype (Vtype (BeeTypes.Tint I32 Unsigned dattr)) 2 dattr)
                                                           (Const (ConsInt (Int.repr 1)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)) ::
                                                            Const (ConsInt (Int.repr 1)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                      (BeeTypes.Atype (Vtype (BeeTypes.Tint I32 Unsigned dattr)) 2 dattr))
                                                (Const (ConsInt (Int.repr 0)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Vtype (BeeTypes.Tint I32 Signed dattr));
                                   is_ebpf := false |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_array)), None) :: nil.

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

Compute (type_check_program example1). *) (* Type checks *)
