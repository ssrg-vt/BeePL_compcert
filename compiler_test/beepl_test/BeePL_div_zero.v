Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     unsigned int x = 10;
     unsigned int y = 0;
     unsigned int r = x / y;   
     return r;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_main, "main") :: nil).

Definition f_div_zero : BeePL.function := {| 
                                   fn_return := tint32u;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tint32u) :: 
                                               (_y, tint32u) :: 
                                               (_r, tint32u) :: nil);
                                   fn_body := Bind 
                                                (_x) tint32u
                                                (cint (Int.repr 10) tint32u)
                                                (Bind 
                                                   (_y) tint32u
                                                   (cint (Int.repr 0) tint32u)
                                                   (Bind 
                                                      (_r) tint32u
                                                      (Prim (Bop Cop.Odiv) 
                                                            (Var _x tint32u :: 
                                                             Var _y tint32u :: nil) tint32u)
                                                      (Var _r tint32u) tint32u) tint32u) tint32u;
                                  is_ebpf := false |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_div_zero))) :: nil.

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
