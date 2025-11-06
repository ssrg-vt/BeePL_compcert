Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
Require Import BeePL_Check_Reserved_Struct BeePL_Bytes_Struct BeePL_Csyntax BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _xc : ident := $"xc".
Definition _xc_end : ident := $"xc_end".
Definition _xc_bee : ident := $"xc_bee".
Definition _copy_from_x_bee : ident := $"copy_from_xc_bee".
Definition _copy_from_x : ident := $"copy_from_xc".
Definition _copy_to_x : ident := $"copy_to_x".
Definition _i : ident := $"i".
Definition _ct : ident := $"ct".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_x, "x") :: 
                                                       (_y, "y") ::
                                                       (_xc, "xc") ::
                                                       (_xc_end, "xc_end") ::
                                                       (_copy_from_x_bee, "copy_from_x_bee") ::
                                                       (_copy_from_x, "copy_from_x") ::
                                                       (_copy_to_x, "copy_to_x") :: (_i, "i") :: (_ct,"ct") ::
                                                       (_main, "main") :: nil).

Definition bcomposites_copy_from_x_bee : list bcomposite_definition :=
(Bcomposite _copy_from_x_bee Struct 
  (Member_plain _xc_bee Bytes :: nil) noattr :: nil).

Definition bcomposites_copy_from_xc : list bcomposite_definition :=
(Bcomposite _copy_from_x Struct 
  (Member_plain _xc tlongu :: Member_plain _xc_end tlongu :: nil) noattr :: nil).

Definition bcomposites_copy_to_x : list bcomposite_definition :=
(Bcomposite _copy_to_x Struct 
  (Member_plain _x tint32u :: Member_plain _y tint32u :: nil) noattr :: nil).

Definition bcomposites : list bcomposite_definition := bcomposites_copy_from_x_bee ++ bcomposites_copy_from_xc ++ bcomposites_copy_to_x.

Definition f_bytes : BeePL.function := {| fn_return := tint32u;
                                              fn_effect :=  nil;
                                              fn_callconv := cc_default;
                                              fn_args := (_i, Ptrtype (Reftype mem_ident (Bstruct _copy_from_x_bee noattr) noattr)) :: nil;
                                              fn_vars := (_ct, Stype _copy_to_x noattr) :: nil;  
                                              fn_body := Match (Sfield (Var _i (Ptrtype (Reftype mem_ident (Bstruct _copy_from_x_bee noattr) noattr))) _xc_bee Bytes)
                                                               (Pbytes _ct (Stype _copy_to_x noattr) ((_x, tint32u) :: (_y, tint32u) :: nil) :: nil)
                                                               ((Bind _x tint32u 
                                                                     (Sfield (Var _ct (Stype _copy_to_x noattr)) _x tint32u)
                                                                     (Bind _y tint32u
                                                                           (Sfield (Var _ct (Stype _copy_to_x noattr)) _y tint32u)
                                                                           (cint (Int.repr 1) tint32u) tint32u) tint32u) ::
                                                               (cint (Int.repr 0) tint32u) :: nil) tint32u;
                                             is_ebpf := true;|}.
                                                      

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_main, AST.Gfun(BeePL.Internal (f_bytes)), None) :: nil.

Definition public_idents : list ident := (_main :: nil).

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
