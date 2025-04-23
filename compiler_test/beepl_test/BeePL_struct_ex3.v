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
}*)

(* let p1 = (p1.x := 10) in p1.x *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _Point : ident := $"Point".
Definition _p1 : ident := $"p1".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t : ident := $"t".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_Point, "Point") ::
                                                      (_p1, "p1") ::
                                                      (_x, "x") :: 
                                                      (_y, "y") ::
                                                      (*(_t, "t") :: *)
                                                      (_main, "main") :: nil).
Definition f_struct : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_p1, BeeTypes.Stype _Point dattr) (*:: (_t, (Ptype Tunit))*) :: nil);
                                   fn_body := (*Bind _t (Ptype Tunit)*)
                                                    (Prim Massgn ((Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _x 
                                                                  (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr))) ::
                                                              (Const (ConsInt (Int.repr 10)) (Ptype (BeeTypes.Tint I32 Signed dattr))) :: nil)
                                                      (Ptype Tunit))
                                                (*(Sfield (Var _p1 (BeeTypes.Stype _Point dattr)) _x 
                                                (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)))
                                              (Ptype (BeeTypes.Tint I32 Signed dattr))*)
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

Definition example1 : BeePL.program := @mkbprogram bcomposites global_definitions public_idents _main bcomposite_correct ident_to_string.

(*Compute (type_check_program example1). 

Compute (BeePL_Csyntax.BeePL_compcert example1).*)

 


(*  OK
         {|
           Ctypes.prog_defs :=
             (22880918%positive,
             Gfun
               (Ctypes.Internal
                  {|
                    Csyntax.fn_return :=
                      Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |};
                    Csyntax.fn_callconv :=
                      {| cc_vararg := None; cc_unproto := false; cc_structret := false |};
                    Csyntax.fn_params := nil;
                    Csyntax.fn_vars :=
                      (4185%positive,
                      Tstruct 1566385715%positive {| attr_volatile := false; attr_alignas := None |})
                      :: nil;
                    Csyntax.fn_body :=
                      Csyntax.Sdo
                        (Csyntax.Eassign
                           (Csyntax.Efield
                              (Csyntax.Evalof
                                 (Csyntax.Evar 4185%positive
                                    (Tstruct 1566385715%positive
                                       {| attr_volatile := false; attr_alignas := None |}))
                                 (Tstruct 1566385715%positive
                                    {| attr_volatile := false; attr_alignas := None |})) 97%positive
                              (Ctypes.Tint I32 Unsigned
                                 {| attr_volatile := false; attr_alignas := None |}))
                           (Csyntax.Eval
                              (Values.Vint
                                 {| Int.intval := 10; Int.intrange := Int.Z_mod_modulus_range' 10 |})
                              (Ctypes.Tint I32 Signed
                                 {| attr_volatile := false; attr_alignas := None |})) Tvoid)
                  |})) :: nil;
           Ctypes.prog_public := 22880918%positive :: nil;
           Ctypes.prog_main := 22880918%positive;
           Ctypes.prog_types :=
             Composite 1566385715%positive Struct
               (Ctypes.Member_plain 97%positive
                  (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |})
                :: Ctypes.Member_plain 98%positive
                     (Ctypes.Tint I32 Unsigned {| attr_volatile := false; attr_alignas := None |})
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
                                                                     (PTree.Node001
                                                                        (PTree.Node001
                                                                        (PTree.Node001 ...)))))))))))))))))))));
           Ctypes.prog_comp_env_eq := eq_refl
         |}
     : res (Ctypes.program Csyntax.function)


*)

