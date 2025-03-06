Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL BeePL_mem BeeTypes BeePL_Csyntax Compiler Errors Extraction. 
From Coq Require Import String List ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.
Local Open Scope error_monad_scope.

(****** Example 1 ******)
(*#include<stdio.h>
   int main() {
        int x = 1;
        int y = 2;
        int r = x + y;
        return r;
   }*)

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "compiler_test/BeePL_progs.v.".
End Info.

Definition dattr := {| attr_volatile := false; attr_alignas := Some 4%N |}.
Definition _x := 1%positive.
Definition _y := 2%positive.
Definition _r := 3%positive.
Definition _main : ident := $"main".

Definition f_main : function := {| fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                               (_y, Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                               (_r, Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil);
                                   fn_body := Bind (_x) 
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Bind (_y) 
                                                   (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Bind (_r) 
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                      (Prim (Bop Cop.Oadd) 
                                                         (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                                          Var _y (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                         (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Var _r (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Ptype Tunit))
                                                (Ptype Tunit) |}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef BeePL.fundef type) := (_main, Gfun(BeePL.Internal f_main)) :: nil.

Definition public_idents : list ident := (_main :: nil).

Lemma composite_default :
build_composite_env nil = OK (PTree.empty composite).
Proof.
unfold build_composite_env; simpl; reflexivity.
Qed.

Definition example1 : BeePL.program := {| prog_defs := global_definitions;
                                          prog_public := public_idents;
                                          prog_main := _main;
                                          prog_types := composites;
                                          prog_comp_env := PTree.empty composite;
                                          prog_comp_env_eq := composite_default |}.


Definition tcp1 := (transf_beepl_program_csyntax (example1)).
Definition tasm1 := transf_beepl_program(example1).

Compute tcp1.
Extraction "tcp1.ml" tcp1.

