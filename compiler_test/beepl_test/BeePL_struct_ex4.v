Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_Csyntax. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <stdio.h>

// Define a struct to represent a point in 2D
struct Point {
    int x;
    int y;
};

int main() {
    struct Point p1;       // Declare a variable of type struct Point
    p1.x = 10;
    return r;
}*)

(* let p1 = (p1.x := 10) in p1.x *)
(* attr_alignas is optional *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _Point : ident := $"Point".
Definition _p1 : ident := $"p1".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t : ident := $"t".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_Point, "Point") ::
                                                      (_p1, "p1") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") ::
                                                      (_t, "t") ::
                                                      (_r, "r") ::
                                                      (_main, "main") :: nil).
Definition f_struct : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p1, BeeTypes.Stype _Point dattr) :: 
                                               (_t, (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) ::
                                               (_r, (Ptype (BeeTypes.Tint I32 Signed dattr))) :: nil);
                                   fn_body := Bind _t (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                (Prim Massgn ((Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _x 
                                                (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) ::
                                                (Const (ConsInt (Int.repr 10)) (Ptype (BeeTypes.Tint I32 Signed dattr))) :: nil)
                                                (Ptype Tunit))
                                               (Bind _r (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                  (Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _x 
                                                 (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                  (Var _r (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                               (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                               (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                |}.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_struct))) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _Point Struct
   (Member_plain _x (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
    Member_plain _y (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil)
   noattr :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

Definition example1 : BeePL.program := @mkbprogram bcomposites global_definitions public_idents _main bcomposite_correct.

(*Compute (BeePL_Csyntax.BeePL_compcert example1).*)

