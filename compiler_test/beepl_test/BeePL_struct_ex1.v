Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_Csyntax BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <stdio.h>

// Define a struct to represent a point in 2D
struct Point {
    int *x;
    int *y;
};

int main() {
    struct Point *p1;       // Declare a variable of type struct Point
    p1.x := ref 0;
    p1.y := ref 0;
    *p1.x := 10;            // Assign values to fields
    *p1.y := 20;
    return *p1.x;
}*)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _Point : ident := $"Point".
Definition _p1 : ident := $"p1".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _x1 : ident := $"x1".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_Point, "Point") ::
                                                      (_p1, "p1") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_x1, "x1") ::
                                                      (_main, "main") :: nil).

(*Definition f_struct : BeePL.function := {| 
                                   fn_return := tint32u;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p1, tstruct _Point) :: 
                                               (_x1, trint32u) :: nil);
                                   fn_body := Bind _x1 tunit
                                                (Prim Massgn ((Sfield (Var _p1 (tstruct _Point)) _x trint32u) ::
                                                              (Prim Ref (cint (Int.repr 0) tint32u :: nil) trint32u) :: nil)
                                                              tunit)
                                                (Bind _x1 tunit
                                                   (Prim Massgn ((Sfield (Var _p1 (tstruct _Point)) _y trint32u) ::
                                                                 (Prim Ref (cint (Int.repr 0) tint32u :: nil) trint32u) :: nil) tunit)
                                                   (Bind _x1 tunit 
                                                      (Prim Massgn (Prim Deref ((Sfield (Var _p1 (tstruct _Point)) _x trint32u) :: nil) trint32u ::
                                                                    (cint (Int.repr 10) tint32u) :: nil) tunit)
                                                      (Bind _x1 tunit 
                                                         (Prim Massgn (Prim Deref ((Sfield (Var _p1 (tstruct _Point)) _y trint32u) :: nil) trint32u ::
                                                                      (cint (Int.repr 20) tint32u) :: nil) tunit)
                                                         (Prim Deref ((Sfield (Var _p1 (tstruct _Point)) _x trint32u) :: nil) tint32u)
                                                         tint32u)
                                                      tint32u)
                                                   tint32u)
                                              tint32u

                                  |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_struct))) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _Point Struct
   (Member_plain _x trint32u :: 
    Member_plain _y trint32u :: nil)
   noattr :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor.
Qed. *)

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.*)

(*Compute (type_check_expr beepl_ef_env example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_struct.(fn_args)) f_struct.(fn_vars)) empty_context f_struct.(fn_body)).

Compute (type_check_program example1). *) (* Type checks *)


(*Definition example1 : BeePL.program := @mkbprogram bcomposites global_definitions public_idents _main bcomposite_correct.

Compute (type_check_program example1). (* debug why typecheck fails *)

Compute (BeePL_Csyntax.BeePL_compcert example1).*)

