Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL BeePL_mem BeeTypes BeePL_Csyntax Compiler Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

(****** Example 1 ******)
(*#include<stdio.h>
   int main() {
        int x = 1;
        int y = 2;
        int r = x + y;
        return r;
   }*)
Definition x := {| vname := 1%positive; vtype := Ptype (Tint BeeTypes.I32 Unsigned) |}.
Definition y := {| vname := 2%positive; vtype := Ptype (Tint BeeTypes.I32 Unsigned) |}.
Definition r := {| vname := 3%positive; vtype := Ptype (Tint BeeTypes.I32 Unsigned) |}.
Definition main := 4%positive.

Definition main_body := Bind (x.(vname)) 
                             (Ptype (Tint I32 Unsigned))
                             (Const (ConsInt (Int.repr 1)) (Ptype (Tint I32 Unsigned)))
                             (Bind (y.(vname)) 
                                   (Ptype (Tint I32 Unsigned))
                                   (Const (ConsInt (Int.repr 2)) (Ptype (Tint I32 Unsigned)))
                                   (Bind (r.(vname)) 
                                         (Ptype (Tint I32 Unsigned))
                                         (Prim (Bop Plus) 
                                               (Var x  :: Var y :: nil)
                                               (Ptype (Tint I32 Unsigned)))
                                         (Var r)
                                         (Ptype (Tint I32 Unsigned)))
                             (Ptype Tunit))
                        (Ptype Tunit). 
                                   
Definition f_main : decl := Fdecl {| fname := main;
                                     args := nil;
                                     lvars := (x :: y :: r :: nil);
                                     rtype := (Ptype (Tint I32 Unsigned));
                                     body := main_body |}.

Definition example1 : module := ((main, f_main) :: nil, main).

Compute (transf_beepl_program_csyntax (example1)).

(* Generated output *)
(*      = Errors.OK
         {|
           prog_defs :=
             (4%positive,
             Gfun
               (Internal
                  {|
                    Csyntax.fn_return := Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |};
                    Csyntax.fn_callconv := {| cc_vararg := Some 0%Z; cc_unproto := false; cc_structret := false |};
                    Csyntax.fn_params := nil;
                    Csyntax.fn_vars :=
                      (1%positive, Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |})
                      :: (2%positive, Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |})
                         :: (3%positive, Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}) :: nil;
                    Csyntax.fn_body :=
                      Csyntax.Ssequence
                        (Csyntax.Sdo
                           (Csyntax.Eassign
                              (Csyntax.Evar 1%positive (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                              (Csyntax.Eval (Values.Vint {| Int.intval := 1; Int.intrange := Int.Z_mod_modulus_range' 1 |})
                                 (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |})) Tvoid))
                        (Csyntax.Sdo
                           (Csyntax.Ecomma
                              (Csyntax.Eassign
                                 (Csyntax.Evar 2%positive
                                    (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (Csyntax.Eval (Values.Vint {| Int.intval := 2; Int.intrange := Int.Z_mod_modulus_range' 2 |})
                                    (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                              (Csyntax.Ecomma
                                 (Csyntax.Eassign
                                    (Csyntax.Evar 3%positive
                                       (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                    (Csyntax.Ebinop Cop.Oadd
                                       (Csyntax.Evar 1%positive
                                          (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                       (Csyntax.Evar 2%positive
                                          (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                       (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                    (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (Csyntax.Evar 3%positive
                                    (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                                 (Ctypes.Tint Ctypes.I32 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 4%N |}))
                              (Ctypes.Tint Ctypes.I8 Ctypes.Unsigned {| attr_volatile := false; attr_alignas := Some 1%N |})))
                  |})) :: nil;
           prog_public := nil;
           prog_main := 4%positive;
           prog_types := nil;
           prog_comp_env := PTree.Empty;
           prog_comp_env_eq := composite_default
         |}
     : Errors.res Csyntax.program *)

Definition asm1 := 
transf_beepl_program(example1).


