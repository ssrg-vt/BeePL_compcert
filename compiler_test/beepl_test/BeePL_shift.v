Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* https://git.kernel.org/pub/scm/linux/kernel/git/netdev/net-next.git/commit/?id=f2d67fec0b43edce8c416101cdc52e71145b5fef *)
(* CVE-2020-8835 *)
(* int bug_example() {
    __u64 r = 0x30303030;
    r = r >> r; // Vulnerability: shift by a large value (undefined behavior)

    return r;
}
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_r, "r") :: 
                                                       (_main, "main") :: nil).

Definition f_rshift : BeePL.function := {| 
                                   fn_return := tlongu;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, tlongu) :: nil);
                                   fn_body := Bind 
                                                (_r) tlongu
                                                (clong (Int64.repr 808464432) tlongu)
                                                (Bind 
                                                   (_r) tlongu
                                                      (Prim (Bop Cop.Oshr) 
                                                            (Var _r tlongu :: 
                                                             Var _r tlongu :: nil) tlongu)
                                                      (Var _r tlongu) tlongu) tlongu;
                                  is_ebpf := false |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_rshift))) :: nil.

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
