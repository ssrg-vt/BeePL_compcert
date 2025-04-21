
Require Import AST Maps Ctypes.
Require Import BeePL BeeTypes Errors BeePL_typechecker Csyntaxdefs. 
From Coq Require Import String.

Require Import BeePL_add BeePL_cond BeePL_app BeePL_div_zero BeePL_struct_ex1 BeePL_struct_ex2 BeePL_struct_ex3 BeePL_struct_ex4 BeePL_for_ex1 BeePL_div_zero1 BeePL_for_ex2.

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

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   BeePL_add.global_definitions 
                                                   BeePL_add.public_idents 
                                                   BeePL_add._main 
                                                   bcomposite_default.*)

Definition example1 : BeePL.program := @mkbprogram BeePL_for_ex2.bcomposites 
                                                   BeePL_for_ex2.global_definitions 
                                                   BeePL_for_ex2.public_idents 
                                                   BeePL_for_ex2._main 
                                                   BeePL_for_ex2.bcomposite_correct.

(*Definition example1 : BeePL.program := {| prog_defs := BeePL_add.global_definitions; (* <-- MODIFY *)
                                          prog_public := BeePL_add.public_idents;    (* <-- MODIFY *)
                                          prog_main := BeePL_add._main;              (* <-- MODIFY *)
                                          prog_types := composites;
                                          prog_comp_env := PTree.empty bcomposite;
                                          prog_comp_env_eq := bcomposite_default |}.*)


Definition example1_atom_of_string : list (ident * string) := BeePL_for_ex2.atom_of_string. (* <-- MODIFY *)

(*Compute (type_check_program example1).*)

