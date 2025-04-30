Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
     unsigned int x = 1;
     unsigned int y = 2;
     unsigned int r = x + y;
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

Definition f_add : BeePL.function := {| 
                                   fn_sec := None;
                                   fn_return := (Vtype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Vtype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_y, BeeTypes.Vtype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_r, BeeTypes.Vtype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Vtype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Const (ConsInt (Int.repr 1)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Bind 
                                                   (_y) 
                                                   (Vtype (BeeTypes.Tint I32 Unsigned dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Bind 
                                                      (_r) 
                                                      (Vtype (BeeTypes.Tint I32 Unsigned dattr))
                                                      (Prim (Bop Cop.Oadd) 
                                                            (Var _x (Vtype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                                             Var _y (Vtype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                            (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Var _r (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Vtype (BeeTypes.Tint I32 Unsigned dattr));
                                    is_ebpf := false|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_add))) :: nil.

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

Compute (type_check_program example1).*) (* Type checks *)




