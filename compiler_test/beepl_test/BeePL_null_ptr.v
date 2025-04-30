Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* Just for testing the functionality of match, none, and some, it will only work when we have r from helper function *)
(* Match should be only performed on pointers coming from helper function *)
(* int main() {
     int t;
     option<int> r;
     t = match r 
         | None  => -1 (* I want to produce error msg with string *)
         | Some x => !r;
     return t;
  }
*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _h : ident := $"h".
Definition _t : ident := $"t".
Definition _p : ident := $"p".
Definition _r : ident := $"r".
Definition _null_ptr : ident := $"null_ptr".
Definition _ptr_add : ident := $"ptr_add".
Definition _ptr_assgn : ident := $"ptr_assgn".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_t, "t") :: 
                                                       (_p, "p") ::
                                                       (_r, "r") ::
                                                       (_null_ptr, "null_ptr") ::
                                                       (_ptr_add, "ptr_add") ::
                                                       (_ptr_assgn, "ptr_assgn") ::
                                                       (_main, "main") :: nil).

Definition f_null_ptr : BeePL.function := {| 
                                   fn_sec := None;
                                   fn_return := tint32s;
                                   fn_effect := Read mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, toint32s) :: (_t, tint32s) :: nil);
                                   fn_body := Bind _t tint32s
                                               (Match (Var _r (toint32s)) 
                                                      (Pnone :: Psome _p :: nil) 
                                                      (cint (Int.repr (-1)%Z) tint32s ::
                                                        (Prim (Deref) (Var _r (toint32s) :: nil) tint32s) :: nil) tint32s)
                                               (Var _t tint32s) tint32s;
                                   is_ebpf := false|}.


(* int main() {
     int t;
     option<int> r;
     t = match r 
         | None  => -1 
         | Some x => (star r + 1);
     return t;
  }
*)

Definition f_ptr_add : BeePL.function := {| 
                                   fn_sec := None;
                                   fn_return := tint32s;
                                   fn_effect := Read mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, toint32s) :: (_t, tint32s) :: nil);
                                   fn_body := Bind _t tint32s
                                               (Match (Var _r (toint32s)) 
                                                      (Pnone :: Psome _p :: nil) 
                                                      (cint (Int.repr (-1)%Z) tint32s ::
                                                       (Prim (Bop Cop.Oadd) 
                                                           (Prim (Deref) (Var _r (toint32s) :: nil) tint32s ::
                                                            cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tint32s)
                                               (Var _t tint32s) tint32s;
                                   is_ebpf := false |}.


(* int main() {
     option<int> r;
     match r 
         | None  => -1 
         | Some x => star r = (star r + 1);
     return 0;
  }
*)

Definition f_ptr_assgn : BeePL.function := {| 
                                   fn_sec := None;
                                   fn_return := tint32s;
                                   fn_effect := Read mem_ident :: Write mem_ident :: Read mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, toint32s) :: (_t, tint32s) :: nil);
                                   fn_body := 
                                               (Match (Var _r (toint32s)) 
                                                      (Pnone :: Psome _p :: nil) 
                                                      (cint (Int.repr (-1)%Z) tint32s ::
                                                       (Bind _t tint32s
                                                        (Prim Massgn 
                                                         (Var _r (toint32s) ::
                                                          (Prim (Bop Cop.Oadd) 
                                                           (Prim (Deref) (Var _r (toint32s) :: nil) tint32s ::
                                                            cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tunit)
                                                         (Prim Deref (Var _r (toint32s) :: nil) tint32s) tint32s) :: nil) tint32s);
                                  is_ebpf := false|}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_null_ptr, AST.Gfun(BeePL.Internal (f_null_ptr))) :: 
      (_ptr_add, AST.Gfun(BeePL.Internal (f_ptr_add))) :: 
      (_main, AST.Gfun(BeePL.Internal (f_ptr_assgn))) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.

Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.

(*Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_ptr_assgn.(fn_args)) f_ptr_add.(fn_vars)) empty_context f_ptr_assgn.(fn_body)).

Compute (type_check_program example1). *) (* Type Checks! *)
