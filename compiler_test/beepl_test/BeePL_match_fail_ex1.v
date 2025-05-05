Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux BeePL_notations.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* int main() {
   option<int> r;
   y = match r with
        | None => 0
        | Some x => !r
   return y; }
*)
(*
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _r : ident := $"r".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t : ident := $"t".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_r, "r") :: 
                                                       (_x, "x") ::
                                                       (_y, "y") ::
                                                       (_t, "t") ::
                                                       (_main, "main") :: nil).

Definition f_option1 : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := Write mem_ident :: Read mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, toption tint32s) :: 
                                               (_x, tint32s) ::
                                               (_y, tint32s) :: 
                                               (_t, tint32s) :: nil);
                                   fn_body := Bind _r (toption tint32s)
                                               (Bind _y tint32s 
                                                     (Match (Var _r (toption tint32s))
                                                              (Pnone :: Psome _x :: nil) 
                                                              (cint (Int.repr 0) tint32s ::
                                                               Prim Deref (Var _r (toption tint32s) :: nil) tint32s :: nil) tint32s) 
                                                     (Var _y tint32s) tint32s) tint32s |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_option1))) :: nil.

Definition public_idents : list ident := (_main :: nil).


Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.*)

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.*)

(*Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_option1.(fn_args)) f_option1.(fn_vars)) empty_context f_option1.(fn_body)).
Compute (type_check_program example1). *) (* Type checks *)
