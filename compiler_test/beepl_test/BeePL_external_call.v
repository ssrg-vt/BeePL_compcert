Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_notations BeePL_typechecker. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*  extern int add(int, int* );
 *     
 *  int main(void) {
 *    int a = 1;
 *    int b = 2;
 *    int c = add(a, &b);
 *    return c;
 *  } 
 *
 *)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _add : ident := $"add".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_a, "a") :: 
                                                      (_b, "b") :: 
                                                      (_c, "c") ::
                                                      (_add, "add") :: 
                                                      (_main, "main") :: nil).

Definition prim_expr : BeePL.expr := Prim (Ref) 
                                          (Var _b tint32s :: nil) trint32s.

Definition test : BeePL.expr := (App (Var _add (tfun (tint32s :: trint32s :: nil)(* args type signature *)
                                                      (nil) (* effect *)
                                                      tint32s)) (* return type *)
                                     (Var _a tint32s :: 
                                      Prim (Ref) 
                                           (Var _b tint32s :: nil) trint32s :: nil) tint32s).

Definition f_external_call : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := (Alloc :: nil);
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_a, tint32s) :: 
                                               (_b, tint32s) :: 
                                               (_c, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_a) tint32s
                                                (cint (Int.repr 1) tint32s) 
                                                (Bind 
                                                   (_b) tint32s
                                                   (cint (Int.repr 2) tint32s) 
                                                   (Bind 
                                                      (_c) tint32s 
                                                      (App (Var _add (Ftype (tint32s :: trint32s :: nil) (* args type signature *)
                                                                            (nil) (* effect *)
                                                                            tint32s)) (* return type *)
                                                           (Var _a tint32s :: 
                                                            Prim (Ref) 
                                                                 (Var _b tint32s :: nil) trint32s :: nil) tint32s)
                                                      (Var _c tint32s) tint32s) tint32s) tint32s;
                                   is_ebpf := false |}.


Definition add_external_function : BeePL.external_function
   := EF_external "add" 
      {| bsig_args := tint32s :: trint32s :: nil;
         bsig_ef := nil;
         bsig_res := tint32s;
         bsig_cc := cc_default
      |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_add, AST.Gfun(BeePL.External (add_external_function) (tint32s :: trint32s :: nil) tint32s 
                                     (cc_default)), None) :: 
      (_main, AST.Gfun(BeePL.Internal (f_external_call)), None):: nil.

Definition public_idents : list ident := (_main :: _add :: nil).

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
                         (bind_vars (bind_vars empty_context f_external_call.(fn_args)) f_external_call.(fn_vars)) empty_context f_external_call.(fn_body)).

Compute (type_check_program example1). *) (* Type checks *)
