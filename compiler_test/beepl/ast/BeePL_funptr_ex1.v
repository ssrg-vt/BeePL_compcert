Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*

int add(int a, int b) {
    return a + b;
}


int compute(int x, int y, int (star fp)(int, int) {
     return fp(x,y);
}

int main() {
    int result = compute(3, 4, add);// Output: Result: 7
    return result;
}*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _fp : ident := $"fp".
Definition _h : ident := $"h". 
Definition _add : ident := $"add".
Definition _compute : ident := $"compute".
Definition _main : ident := $"main".


Definition  ident_to_string : list (ident * string) := ((_a, "a") :: 
                                                        (_b, "b") :: 
                                                        (_c, "c") ::
                                                        (_x, "x") :: 
                                                        (_y, "y") :: 
                                                        (_r, "r") ::
                                                        (_fp, "fp") ::
                                                        (_add, "add") ::
                                                        (_compute, "compute") ::
                                                        (_main, "main") :: nil).


Definition f_add : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, tint32s) :: 
                                               (_y, tint32s) :: nil);
                                   fn_vars := ((_r, tint32s) :: nil);
                                   fn_body := Bind 
                                                (_r) tint32u
                                                (Prim (Bop Cop.Oadd) 
                                                      (Var _x tint32s :: 
                                                       Var _y tint32s :: nil) tint32s)
                                                (Var _r tint32s) tint32s;
                                   is_ebpf := false |}.


Definition f_compute : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := ((_x, tint32s) :: 
                                               (_y, tint32s) :: 
                                               (_fp, (tpfun (tint32s :: tint32s :: nil) nil tint32s false)) :: nil); 
                                   fn_vars := nil;
                                   fn_body := (App (Var _fp (tpfun (tint32s :: tint32s :: nil) nil tint32s false))
                                                   (Var _x tint32s :: 
                                                    Var _y tint32s :: nil) tint32s);
                                   is_ebpf := false |}.


Definition f_main : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_r, tint32s) :: nil);
                                   fn_body := 
                                              Bind 
                                                   (_r) tint32s
                                                   (App (Var _compute (tfun (tint32s :: tint32s :: tpfun (tint32s :: tint32s :: nil) nil tint32s false :: nil) 
                                                                       nil tint32s false))
                                                        (cint (Int.repr 3) tint32s ::
                                                         cint (Int.repr 4) tint32s ::
                                                         Var _add (tfun (tint32s :: tint32s :: nil) nil tint32s false) :: nil) 
                                                         tint32s)
                                                   (Var _r tint32s) tint32s; 
                                   is_ebpf := false |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_add, AST.Gfun(BeePL.Internal (f_add)), None) ::
      (_compute, AST.Gfun(BeePL.Internal (f_compute)), None) ::
      (_main, AST.Gfun(BeePL.Internal (f_main)), None) :: nil.

Definition public_idents : list ident := (_main :: _compute :: _add :: nil).

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


