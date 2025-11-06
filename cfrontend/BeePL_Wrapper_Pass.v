Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations BeePL_bpf.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct BeePL_Check_Reserved_Struct.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

Definition get_struct_name (c : composite_definition) : ident :=
match c with 
| Composite s su m a => s
end.

Definition check_member_name (m : member) : bool :=
match m with 
| Ctypes.Member_plain mn t => if ident_eq mn _data_bee then true else false 
| Ctypes.Member_bitfield mn _ _ _ _ _ => if ident_eq mn _data_bee then true else false
end.

Fixpoint transform_bytes_data_data_end (ms : members) : members :=
match ms with 
| nil => nil
| m :: ms1 => if check_member_name m 
              then Ctypes.Member_plain _data (Ctypes.Tint I32 Unsigned noattr)  :: 
                   Ctypes.Member_plain (ident_of_string "data_end") (Ctypes.Tint I32 Unsigned noattr) ::
                   transform_bytes_data_data_end ms1 
              else m :: transform_bytes_data_data_end ms1
end.

Definition transform_struct_bee_decl_ebpf_decl (c : composite_definition) : list composite_definition :=
match c with 
| Composite s su m a => if ident_eq s _xdp_md_bee (* add more if cases when we deal with other structs like sk_buff *)
                        then Composite (ident_of_string "xdp_md") Struct (transform_bytes_data_data_end m) a :: c :: nil
                        else c :: nil
end.

Fixpoint wrapper_beepl_struct_ebpf_struct (cs : list composite_definition) : list composite_definition :=
match cs with 
| nil => nil
| c1 :: cs1 => transform_struct_bee_decl_ebpf_decl c1 ++ wrapper_beepl_struct_ebpf_struct cs1
end.


Definition transform_ctx_ebpf_ctx (args : list (ident * type)) : res (list (ident * Ctypes.type)) :=
let i := (ident_of_string "ctx") in
match args with 
| nil => OK nil
| (i, t) :: nil => 
  if eq_type t (Ptrtype (Otype (Reftype mem_ident (Bstruct  _xdp_md_bee noattr) noattr))) 
  then OK ((ident_of_string "ctx", Tpointer (Tstruct (ident_of_string "xdp_md") noattr) noattr) :: nil)
  else OK ((i, (transBeePL_type t)) :: nil)
| _ => Error (msg "COMPILER ERROR: eBPF program should take only one argument (context)")
end.


