Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <stdio.h>

int main() {
    int x = 0;
    for (int i = 5; i <= 1; i--) {
            x = x + 1;
    }
}
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _i : ident := $"i".
Definition _t : ident := $"t".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_i, "i") :: 
                                                      (_t, "t") ::
                                                      (_main, "main") :: nil).

Definition f_for : BeePL.function := {| 
                                   fn_return := (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr);
                                   fn_effect := (Read $"h" :: Write $"h" :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr)) :: 
                                               (_i, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_t, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
                                   fn_body := (Bind _x (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr) 
                                                       (Const (ConsInt (Int.repr 0)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                       (Bind _t (Ptype Tunit)
                                                          (For _i 
                                                             (Const (ConsInt (Int.repr 5)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                             (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                             Down
                                                             (Prim Massgn (Var _x (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr) ::
                                                                     (Prim (Bop Cop.Oadd) 
                                                                        (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                                                           Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                                        (Ptype (BeeTypes.Tint I32 Unsigned dattr))) :: nil)
                                                            (Ptype Tunit))
                                                          (Ptype Tunit))
                                                     (Var _x (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr))
                                                     (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr))
                                                 (Reftype $"h" (Bprim (BeeTypes.Tint I32 Unsigned dattr)) dattr))|}.


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

(*Definition example1 : BeePL.program := @mkbprogram BeePL_for_ex2.bcomposites 
                                                   BeePL_for_ex2.global_definitions 
                                                   BeePL_for_ex2.public_idents 
                                                   BeePL_for_ex2._main 
                                                   BeePL_for_ex2.bcomposite_correct.

Compute (type_check_program example1).*)
