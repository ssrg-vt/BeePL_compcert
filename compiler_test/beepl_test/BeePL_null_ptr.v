Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* Just for testing the functionality of match, none, and some *)
(* This program will never type check in BeePL as programmer is not suppose to do match on ref(2) *)
(* Match should be only performed on pointers coming from helper function *)
(* int main() {
     match ref(2) 
     | None option<ref<int>> => -1 (* I want to produce error msg with string *)
     | Some x => let r = !(ref(2)) in r
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _h : ident := $"h".
Definition _p : ident := $"p".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_p, "p") :: 
                                                       (_r, "r") ::
                                                       (_main, "main") :: nil).

Definition f_null_ptr : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p, toption (trint32s)) :: 
                                               (_r, tint32s) :: 
                                                nil);
                                   fn_body := Match (Prim (Ref) (cint (Int.repr 2) tint32s :: nil) trint32s) 
                                               (Pnone :: Psome _p :: nil) 
                                               (cint (Int.repr 2) tint32s ::
                                                Bind _r tint32s
                                                            (Prim (Deref) 
                                                               (Prim (Ref) (cint (Int.repr 2) tint32s :: nil) trint32s :: nil) tint32s) 
                                                            (Var _r tint32s) tint32s :: nil) tint32s |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_null_ptr))) :: nil.

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

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_null_ptr.(fn_args)) f_null_ptr.(fn_vars)) empty_context f_null_ptr.(fn_body)).

Compute (type_check_program example1). Does not type check: Expected behavior *)
