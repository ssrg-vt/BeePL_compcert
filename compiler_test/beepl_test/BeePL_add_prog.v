Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes.
Require Import BeePL BeePL_mem BeeTypes BeePL_Csyntax BeePL_values Compiler Errors Extraction. 
From Coq Require Import String List ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.
Local Open Scope error_monad_scope.

(* At the end of the file you will see two definitions. One for example1 and the
   other for example1_atom_of_string. Those two definitions are extracted to 
   OCaml by extraction.v and can be used in Driver.ml during compilation. 
   example1 is a BeePL.program and example1_atom_of_string maps variable and 
   function identifiers to variable and function names. Both definitions are 
   required to produce an executable. The definitions are used by process_b_file
   in Driver.ml.

   Modify the definitions to change the program that gets compiled.

   To compile the program invoke ccomp with a file that has the file extension
   `.b`. The file can be empty. When CompCert sees a file ending in `.b` it will
   call process_b_file and process example1_atom_of_string then convert example1
   to csyntax.
*)


(* int main() {
     unsigned int x = 1;
     unsigned int y = 2;
     unsigned int r = x + y;
     return r;
  }
*)

(* attr_alignas is optional *)
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _r : ident := $"r".
Definition _main : ident := $"main".

Definition f_main_atom_of_string : list (ident * string) := ((_x, "x") :: 
                                                             (_y, "y") :: 
                                                             (_r, "r") :: 
                                                             (_main, "main") :: nil).

Definition f_bind : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_y, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
                                               (_r, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
                                   fn_body := Bind 
                                                (_x) 
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Bind 
                                                   (_y) 
                                                   (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                   (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Bind 
                                                      (_r) 
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                      (Prim (Bop Cop.Oadd) 
                                                            (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: 
                                                             Var _y (Ptype (BeeTypes.Tint I32 Unsigned dattr)) :: nil)
                                                            (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Var _r (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                   (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr)) |}.

(* int main() {
     unsigned int x = 1;
  }
*)

Definition f_assign1 : BeePL.function := {|
   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
   fn_effect := nil;
   fn_callconv := cc_default;
   fn_args := nil;
   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
   fn_body := Bind
               (_x)
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
               (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
               (Const (ConsInt (Int.repr 0)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))  (* Should be return expr *)
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
   |}.


Definition f_assign1_unit : BeePL.function := {|
   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
   fn_effect := nil;
   fn_callconv := cc_default;
   fn_args := nil;
   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
   fn_body := Bind
               (_x)
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
               (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
               (Unit (Ptype Tunit))  (* Should be return expr *)
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
   |}.

(* int main() {
     unsigned int x = 1;
     unsigned int y = 2;
     return x;
   }
*)

Definition f_assign2 : BeePL.function := {|
   fn_return := (Ptype (BeeTypes.Tint I32 Signed dattr));
   fn_effect := nil;
   fn_callconv := cc_default;
   fn_args := nil;
   fn_vars := ((_x, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) ::
               (_y, BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil);
   fn_body := Bind
               (_x)
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
               (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
               (Bind 
                 (_y) 
                 (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                 (Const (ConsInt (Int.repr 2)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                 (Var _x (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                 (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
               (Ptype (BeeTypes.Tint I32 Unsigned dattr))
   |}.


(* Construct the BeePL.program *)

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) := (_main, AST.Gfun(BeePL.Internal (f_assign1_unit))) :: nil.

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

Definition example1_atom_of_string : list (ident * string) := f_main_atom_of_string.


(*Compute (transf_beepl_program_csyntax (example1)).*)
