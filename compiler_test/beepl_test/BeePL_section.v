Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
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
Definition _val : ident := $"val".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_r, "r") :: 
                                                      (_val, "val") ::
                                                      (_main, "main") :: nil).

Definition v_val : AST.globvar type := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_add : BeePL.function := {| 
                                   fn_return := (tint32s);
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, tint32s) :: 
                                               (_y, tint32s) :: 
                                               (_r, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (tint32s)
                                                (Const (ConsInt (Int.repr 1)) (tint32s))
                                                (Bind 
                                                   (_y) 
                                                   (tint32s)
                                                   (Const (ConsInt (Int.repr 2)) (tint32s))
                                                   (Bind 
                                                      (_r) 
                                                      (tint32s)
                                                      (Prim (Bop Cop.Oadd) 
                                                            (Var _x (tint32s) :: 
                                                             Var _y (tint32s) :: nil)
                                                            (tint32s))
                                                      (Var _r (tint32s))
                                                      (tint32s))
                                                   (tint32s))
                                                (tint32s); 
                                   is_ebpf := false|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_val, Gvar v_val, Some "license") :: (_main, AST.Gfun(BeePL.Internal (f_add)), Some "xdp") :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.
