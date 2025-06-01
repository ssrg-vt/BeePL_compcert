Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
Require Import BeePL_Check_Reserved_Struct BeePL_Bytes_Struct BeePL_Csyntax BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                       (_main, "main") :: nil).

Definition f_bytes : BeePL.function := {| fn_return := tint32s;
                                           fn_effect :=  nil;
                                           fn_callconv := cc_default;
                                           fn_args := nil;
                                           fn_vars := ((_x, Bytes) :: nil);  
                                           fn_body := (Bind _x Bytes
                                                         (Unit tunit)
                                                         (Unit tunit) tunit)
                                                       |}.
                                                      

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_bytes)), None) :: nil.

Definition public_idents : list ident := (_main :: nil).

Definition bcomposites : list bcomposite_definition := nil.
(*(Bcomposite _bytes_t Struct
   (Member_plain _start toint8u :: 
    Member_plain _end toint8u :: nil)
   noattr :: nil).*)

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

Definition example1 : BeePL.program := @mkbprogram BeePL_bytes1.bcomposites 
                                                   BeePL_bytes1.global_definitions 
                                                   BeePL_bytes1.public_idents 
                                                   BeePL_bytes1._main 
                                                   BeePL_bytes1.bcomposite_correct
                                                   BeePL_bytes1.ident_to_string.

(*Compute (check_struct_from_program example1).*) 
