Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL BeePL_mem BeeTypes BeePL_Csyntax Compiler Errors Extraction.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.



(****** Example 1 ******)
(*#include<stdio.h>
   int main() {
        return 2;
   }*)

Definition dattr := {| attr_volatile := false; attr_alignas := Some 4%N |}.
Definition main := 1%positive.

Definition main_body := Val (Vint (Int.repr 2)) (Ptype (Tint I32 Unsigned dattr)). 
               
Definition f_main : function := {| fn_return := (Ptype (Tint I32 Unsigned dattr));
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := nil;
                                   fn_body := main_body |}.

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef fundef type) := (main, Gfun(Internal f_main)) :: nil.

Definition public_idents : list ident := (main :: nil).

Lemma composite_default :
build_composite_env nil = OK (PTree.empty composite).
Proof.
unfold build_composite_env; simpl; reflexivity.
Qed.

Definition texample1 : BeePL.program := {| prog_defs := global_definitions;
                                           prog_public := public_idents;
                                           prog_main := main;
                                           prog_types := composites;
                                           prog_comp_env := PTree.empty composite;
                                           prog_comp_env_eq := composite_default |}.


Definition tcp1 := (transf_beepl_program_csyntax (texample1)).
Definition tasm1 := transf_beepl_program(texample1).

