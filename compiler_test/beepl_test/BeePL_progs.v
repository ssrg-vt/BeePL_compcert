Require Import AST Maps Ctypes.
Require Import BeePL BeeTypes Errors BeePL_typechecker Csyntaxdefs. 
From Coq Require Import String.

Require Import BeePL_add BeePL_add_ptr BeePL_div_zero1 BeePL_div_zero BeePL_add_ex1
BeePL_cond BeePL_app BeePL_funptr_ex1 BeePL_bpf_get_prandom BeePL_for_ex1 BeePL_for_ex2
BeePL_external_call BeePL_match_fail_ex1 BeePL_null_ptr BeePL_bitstring1 BeePL_globvar1
BeePL_bpf_xdp_packet_count BeePL_bpf_xdp_packet_count1 BeePL_bpf_map_example1 BeePL_bpf_drop_xdp_packet_iPv6
BeePL_bpf BeePL_bpf_handle_tp BeePL_add_ref BeePL_cast BeePL_cast1 BeePL_shift BeePL_bpf_map_null_check. 

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

Definition example1 : BeePL.program := @mkbprogram BeePL_bpf_map_example1.bcomposites 
                                                   BeePL_bpf_map_example1.global_definitions 
                                                   BeePL_bpf_map_example1.public_idents 
                                                   BeePL_bpf_map_example1._hash_map_example
                                                   BeePL_bpf_map_example1.bcomposite_correct
                                                   BeePL_bpf_map_example1.ident_to_string.


