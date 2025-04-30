Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_Csyntax BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*
#include <stdio.h>

// Define a struct to represent a point in 2D
struct Point {
    int *x;
    int *y;
};

int main(void)
{
  struct Point p1;
  *p1.x = 10U;
  return *p1.x;
}
}*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _Point : ident := $"Point".
Definition _p1 : ident := $"p1".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t : ident := $"t".
Definition _p2 : ident := $"p2".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_Point, "Point") ::
                                                      (_p1, "p1") ::
                                                      (_p2, "p2") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") ::
                                                      (_t, "t") ::
                                                      (_main, "main") :: nil).

Definition f_struct : BeePL.function := {| fn_return := tint32s;
                                           fn_effect :=  Write mem_ident :: Read mem_ident :: nil;
                                           fn_callconv := cc_default;
                                           fn_args := nil;
                                           fn_vars := ((_p1, (Reftype mem_ident (Bstruct _Point noattr) noattr)) :: nil);  (* p1 is a struct variable on stack *)
                                           fn_body := Screate _p1 ((_x, (cint (Int.repr 10) tint32s)) :: (_y, (cint (Int.repr 20) tint32s)) :: nil) 
                                                        (Reftype mem_ident (Bstruct _Point noattr) noattr)
                                                       |}.
                                                      

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_struct))) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _Point Struct
   (Member_plain _x tint32s :: 
    Member_plain _y tint32s :: nil)
   noattr :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_struct.(fn_args)) f_struct.(fn_vars)) empty_context f_struct.(fn_body)).

Compute (type_check_program example1). *)



