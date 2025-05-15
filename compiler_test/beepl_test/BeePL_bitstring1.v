Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker.
Require Import BeePL_Check_Reserved_Struct BeePL_Bytes_Struct BeePL_Csyntax BeePL_notations. 
From Coq Require Import String ZArith Lists.List.
From compcert Require Import Csyntaxdefs Errors Maps BeePL_aux.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _xdp_md_bee : ident := $"xdp_md_bee".
Definition _ctx : ident := $"ctx".
Definition _data : ident := $"data".
Definition _data_end : ident := $"data_end".
Definition _data_meta : ident := $"data_meta".
Definition _dstruct : ident := $"dstruct".
Definition _dst : ident := $"dst".
Definition _src : ident := $"src".
Definition _bytes_t : ident := $"bytes_t".
Definition _start : ident := $"start".
Definition _end : ident := $"end".
Definition _cv : ident := $"cv".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_xdp_md_bee, "xdp_md_bee") ::
                                                       (_dstruct, "dstruct") ::
                                                       (_ctx, "ctx") ::
                                                       (_data, "data") ::
                                                       (_data_end, "data_end") ::
                                                       (_data_meta, "data_meta") :: 
                                                       (_dst, "dst") ::
                                                       (_src, "src") ::
                                                       (_cv, "cv") ::
                                                       (_main, "main") :: nil).

Definition f_bytes : BeePL.function := {| fn_return := tint32s;
                                           fn_effect :=  nil;
                                           fn_callconv := cc_default;
                                           fn_args := (_ctx, tpstruct _xdp_md_bee)  :: nil ;
                                           fn_vars := (_cv, Stype _dstruct noattr) :: (_data, Bytes) :: nil;  
                                           fn_body := (*Bind _cv (Stype _dstruct noattr)*)
                                                        (Match (Sfield (Var _ctx (tpstruct _xdp_md_bee)) _data Bytes)  
                                                         (Pbytes _cv (Stype _dstruct noattr) ((_dst, tint32s) :: (_src, tint32s) :: nil) :: nil)  
                                                         (cint (Int.repr 1) tint32s :: cint (Int.repr 2) tint32s :: nil) tint32s);
                                                        (*(Var _cv (Stype _dstruct noattr)) (Stype _dstruct noattr)*)
                                           is_ebpf := true; 
                                                       |}.
                                                      

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_main, AST.Gfun(BeePL.Internal (f_bytes))) :: nil.

Definition public_idents : list ident := (_main :: nil).


Definition bcomposites : list bcomposite_definition :=
 Bcomposite _xdp_md_bee Struct
   (Member_plain _data Bytes :: 
    Member_plain _data_meta tint32u :: nil)
   noattr :: 
 Bcomposite _dstruct Struct 
   (Member_plain _dst tint32s :: 
    Member_plain _src tint32s :: nil)
   noattr :: nil.


Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
unfold wf_bcomposites.
unfold build_bcomposite_env; simpl; constructor. 
Qed.

Definition example1 : BeePL.program := @mkbprogram BeePL_bitstring1.bcomposites 
                                                   BeePL_bitstring1.global_definitions 
                                                   BeePL_bitstring1.public_idents 
                                                   BeePL_bitstring1._main 
                                                   BeePL_bitstring1.bcomposite_correct
                                                   BeePL_bitstring1.ident_to_string.

(*Compute (check_struct_from_program example1).*) 
