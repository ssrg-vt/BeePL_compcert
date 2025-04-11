Require Import AST Maps Ctypes.
Require Import BeePL BeeTypes Errors BeePL_typechecker. 
From Coq Require Import String.

Require Import BeePL_add BeePL_cond BeePL_app BeePL_div_zero.

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

Definition composites : list composite_definition := nil.

Lemma composite_default :
  build_composite_env nil = OK (PTree.empty composite).
Proof.
  unfold build_composite_env; simpl; reflexivity.
Qed.

Definition example1 : BeePL.program := {| prog_defs := BeePL_div_zero.global_definitions; (* <-- MODIFY *)
                                          prog_public := BeePL_div_zero.public_idents;    (* <-- MODIFY *)
                                          prog_main := BeePL_div_zero._main;              (* <-- MODIFY *)
                                          prog_types := composites;
                                          prog_comp_env := PTree.empty composite;
                                          prog_comp_env_eq := composite_default |}.

Definition example1_atom_of_string : list (ident * string) := BeePL_div_zero.atom_of_string. (* <-- MODIFY *)

Compute (type_check_program empty_context empty_context example1).
