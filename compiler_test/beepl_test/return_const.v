Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL_values BeePL BeePL_mem BeeTypes BeePL_Csyntax Compiler Errors Extraction. 
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
        return 5;
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

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _main : ident := $"main".

Definition f_main : function := {| fn_return := (Ptype (BeeTypes.Tlong Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := nil;
                                   fn_body := Const (ConsLong (Int64.repr 5)) (Ptype (BeeTypes.Tlong Unsigned dattr)) |}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef BeePL.fundef type) := (_main, Gfun(BeePL.Internal f_main)) :: nil.

Definition public_idents : list ident := (_main :: nil).

Lemma composite_default :
build_composite_env nil = OK (PTree.empty composite).
Proof.
unfold build_composite_env; simpl; reflexivity.
Qed.

Definition return_example1 : BeePL.program := {| prog_defs := global_definitions;
                                          prog_public := public_idents;
                                          prog_main := _main;
                                          prog_types := composites;
                                          prog_comp_env := PTree.empty composite;
                                          prog_comp_env_eq := composite_default |}.


Definition return_tcp1 := (transf_beepl_program_csyntax (return_example1)).
Definition return_tasm1 := transf_beepl_program(return_example1).

Compute return_tcp1.
Extraction "return_tcp1.ml" return_tcp1.

(**        = OK
         {|
           Ctypes.prog_defs :=
             (22880918%positive,
             Gfun
               (Ctypes.Internal
                  {|
                    Csyntax.fn_return :=
                      Ctypes.Tlong Unsigned
                        {| attr_volatile := false; attr_alignas := None |};
                    Csyntax.fn_callconv :=
                      {|
                        cc_vararg := None; cc_unproto := false; cc_structret := false
                      |};
                    Csyntax.fn_params := nil;
                    Csyntax.fn_vars := nil;
                    Csyntax.fn_body :=
                      Csyntax.Sreturn
                        (Some
                           (Csyntax.Evalof
                              (Csyntax.Eval
                                 (Values.Vlong
                                    {|
                                      Int64.intval := 5;
                                      Int64.intrange := Int64.Z_mod_modulus_range' 5
                                    |})
                                 (Ctypes.Tlong Unsigned
                                    {| attr_volatile := false; attr_alignas := None |}))
                              (Ctypes.Tlong Unsigned
                                 {| attr_volatile := false; attr_alignas := None |})))
                  |})) :: nil;
           Ctypes.prog_public := 22880918%positive :: nil;
           Ctypes.prog_main := 22880918%positive;
           Ctypes.prog_types := nil;
           Ctypes.prog_comp_env := PTree.Empty;
           Ctypes.prog_comp_env_eq := composite_default
         |}
     : res Csyntax.program **)

