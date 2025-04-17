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
    p1.x = 10;             // Assign values to fields
    p1.y = 20;
    return p1.x;
}*)

(* attr_alignas is optional *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _Point : ident := $"Point".
Definition _p1 : ident := $"p1".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _x1 : ident := $"_x1".
Definition _y1 : ident := $"_y1".
Definition _main : ident := $"main".

Definition atom_of_string : list (ident * string) := ((_Point, "Point") ::
                                                      (_p1, "p1") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") :: 
                                                      (_x1, "x1") ::
                                                      (_y1, "y1") :: 
                                                      (_main, "main") :: nil).
Definition f_struct : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p1, BeeTypes.Stype _Point dattr) :: nil);
                                   fn_body := Bind 
                                                (_p1) 
                                                (BeeTypes.Stype _Point dattr)
                                                (Unit (Ptype Tunit))
                                                (Bind 
                                                   (_x1)
                                                   (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                   (Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _x 
                                                           (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                   (Bind 
                                                      (_x1)
                                                      (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                      (Const (ConsInt (Int.repr 10)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                      (Bind 
                                                         (_y1)
                                                         (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                         (Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _y 
                                                                 (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                         (Bind 
                                                            (_y1)
                                                            (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))
                                                            (Const (ConsInt (Int.repr 20)) (Ptype (BeeTypes.Tint I32 Signed dattr)))
                                                            (Var _x1 (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                            (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                         (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                                   (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
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

(*Definition example1 : BeePL.program := @mkbprogram bcomposites global_definitions public_idents _main bcomposite_correct.

Compute (type_check_program example1). (* debug why typecheck fails *)

Compute (BeePL_Csyntax.BeePL_compcert example1).*)

(*  = OK
         {|
           Ctypes.prog_defs :=
             (22880918%positive,
             Gfun
               (Ctypes.Internal
                  {|
                    Csyntax.fn_return := Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |};
                    Csyntax.fn_callconv := {| cc_vararg := None; cc_unproto := false; cc_structret := false |};
                    Csyntax.fn_params := nil;
                    Csyntax.fn_vars :=
                      (4185%positive, Tstruct 1566385715%positive {| attr_volatile := false; attr_alignas := None |}) :: nil;
                    Csyntax.fn_body :=
                      Csyntax.Ssequence
                        (Csyntax.Sdo
                           (Csyntax.Eassign
                              (Csyntax.Evar 4185%positive
                                 (Tstruct 1566385715%positive {| attr_volatile := false; attr_alignas := None |}))
                              (Csyntax.Eval (Values.Vint {| Int.intval := 0; Int.intrange := Int.Z_mod_modulus_range' 0 |}) Tvoid)
                              Tvoid))
                        (Csyntax.Ssequence
                           (Csyntax.Sdo
                              (Csyntax.Eassign
                                 (Csyntax.Evar 268414%positive
                                    (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                 (Csyntax.Efield
                                    (Csyntax.Evar 4185%positive
                                       (Tstruct 1566385715%positive {| attr_volatile := false; attr_alignas := None |}))
                                    97%positive (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                 Tvoid))
                           (Csyntax.Ssequence
                              (Csyntax.Sdo
                                 (Csyntax.Eassign
                                    (Csyntax.Evar 268414%positive
                                       (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                    (Csyntax.Eval
                                       (Values.Vint {| Int.intval := 10; Int.intrange := Int.Z_mod_modulus_range' 10 |})
                                       (Ctypes.Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})) Tvoid))
                              (Csyntax.Ssequence
                                 (Csyntax.Sdo
                                    (Csyntax.Eassign
                                       (Csyntax.Evar 268478%positive
                                          (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                       (Csyntax.Efield
                                          (Csyntax.Evar 4185%positive
                                             (Tstruct 1566385715%positive {| attr_volatile := false; attr_alignas := None |}))
                                          98%positive
                                          (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |})) Tvoid))
                                 (Csyntax.Ssequence
                                    (Csyntax.Sdo
                                       (Csyntax.Eassign
                                          (Csyntax.Evar 268478%positive
                                             (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                          (Csyntax.Eval
                                             (Values.Vint {| Int.intval := 20; Int.intrange := Int.Z_mod_modulus_range' 20 |})
                                             (Ctypes.Tint I32 Signed {| attr_volatile := false; attr_alignas := None |})) Tvoid))
                                    (Csyntax.Sreturn
                                       (Some
                                          (Csyntax.Evalof
                                             (Csyntax.Evar 268414%positive
                                                (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))
                                             (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |}))))))))
                  |})) :: nil;
           Ctypes.prog_public := 22880918%positive :: nil;
           Ctypes.prog_main := 22880918%positive;
           Ctypes.prog_types :=
             Composite 1566385715%positive Struct
               (Ctypes.Member_plain 97%positive (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |})
                :: Ctypes.Member_plain 98%positive (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |})
                   :: nil) {| attr_volatile := false; attr_alignas := None |} :: nil;
           Ctypes.prog_comp_env :=
             PTree.Nodes
               (PTree.Node001
                  (PTree.Node001
                     (PTree.Node100
                        (PTree.Node100
                           (PTree.Node001
                              (PTree.Node001
                                 (PTree.Node100
                                    (PTree.Node100
                                       (PTree.Node100
                                          (PTree.Node001
                                             (PTree.Node001
                                                (PTree.Node100
                                                   (PTree.Node100
                                                      (PTree.Node001
                                                         (PTree.Node100
                                                            (PTree.Node100
                                                               (PTree.Node001
                                                                  (PTree.Node100
                                                                     (PTree.Node001 (PTree.Node001 (PTree.Node001 ...)))))))))))))))))))));
           Ctypes.prog_comp_env_eq := eq_refl
         |}
     : res (Ctypes.program Csyntax.function)
*)

