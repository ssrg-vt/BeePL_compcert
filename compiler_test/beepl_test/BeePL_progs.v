Require Import AST Maps Ctypes.
Require Import BeePL BeeTypes Errors BeePL_typechecker Csyntaxdefs. 
From Coq Require Import String.

Require Import BeePL_add BeePL_add_ptr. 
(* BeePL_cond BeePL_app BeePL_div_zero BeePL_div_zero1 BeePL_external_call BeePL_ref.
Require Import BeePL_struct_ex2 BeePL_for_ex1 BeePL_for_ex2 BeePL_globvar1.
Require Import BeePL_bpf_get_prandom BeePL_bpf_ktime_get_ns.*) (*BeePL_null_ptr BeePL_match_fail_ex1.*)

(* In this file you will see two definitions. One for example1 and the other for
   example1_atom_of_string. Those two definitions are extracted to OCaml by 
   extraction.v and can be used in Driver.ml during compilation. example1 is a 
   BeePL.program and example1_atom_of_string maps variable and function 
   identifiers to variable and function names. Both definitions are required to
   produce an executable. The definitions are used by process_b_file in Driver.ml.

   Modify the definitions to change the program that gets compiled.

   To compile the program invoke ccomp with a file that has the file extension
   `.b`. The file can be empty. When CompCert sees a file ending in `.b` it will
   call process_b_file and process example1_atom_of_string then convert example1
   to csyntax.
*)

(* Construct the BeePL.program *)

Definition bcomposites : list bcomposite_definition := nil.

Lemma bcomposite_default :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; reflexivity.
Qed.

Definition example1 : BeePL.program := @mkbprogram BeePL_add_ptr.bcomposites 
                                                   BeePL_add_ptr.global_definitions 
                                                   BeePL_add_ptr.public_idents 
                                                   BeePL_add_ptr._main 
                                                   BeePL_add_ptr.bcomposite_correct
                                                   BeePL_add_ptr.ident_to_string.


