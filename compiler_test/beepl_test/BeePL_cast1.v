Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=e88b2c6e5a4d9ce30d75391e4d950da74bb2bd90 *)
(* CVE-2021-3600 *)
(* int main() {
     unsigned long x = 0x100000000;
     unsigned int y = 3;
     unsigned int z = (unsigned int)x;
     unsigned int r = y % z;
     return r;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                       (_y, "y") :: 
                                                       (_z, "z") ::
                                                       (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_trun_div : BeePL.function := {| 
                                   fn_return := tint32u;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tlongu) :: 
                                               (_y, tint32u) ::
                                               (_z, tint32u) ::
                                               (_r, tint32u) :: nil);
                                   fn_body := Bind 
                                                (_x) tlongu
                                                (clong (Int64.repr 4294967296) tlongu)
                                                (Bind 
                                                   (_y) tint32u
                                                   (cint (Int.repr 3) tint32u)
                                                   (Bind 
                                                      (_z) tint32u
                                                      (Prim (Cast tint32u) 
                                                            (Var _x tlongu :: nil) tint32u)
                                                      (Bind 
                                                      (_r) tint32u
                                                      (Prim (Bop Cop.Omod) 
                                                            (Var _y tint32u :: 
                                                             Var _z tint32u :: nil) tint32u)
                                                      (Var _r tint32u) tint32u) tint32u) tint32u) tint32u;
                                  is_ebpf := false |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_trun_div)), None) :: nil.

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
