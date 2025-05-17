Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations BeePL_bpf.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct BeePL_Check_Reserved_Struct.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

Fixpoint wrapper_beepl_struct_ebpf_struct (cs : list composite_definition) : list composite_definition :=
match cs with 
| nil => nil
| c1 :: cs1 => match c1 with 
               | (Composite _xdp_md_bee Struct
                   (Ctypes.Member_plain _data_bee (Tstruct bytes_t {| attr_volatile := false; attr_alignas := None |}) :: rest) 
                   {| attr_volatile := false; attr_alignas := None |})
                   => (Composite (ident_of_string "xdp_md") Struct
                        (Ctypes.Member_plain _data (Ctypes.Tint I32 Unsigned noattr)  :: 
                         Ctypes.Member_plain (ident_of_string "data_end") (Ctypes.Tint I32 Unsigned noattr)  :: rest) noattr) :: c1 ::
                       wrapper_beepl_struct_ebpf_struct cs1
              | _ => c1 :: wrapper_beepl_struct_ebpf_struct cs1
              end
end.


Fixpoint transform_ctx_ebpf_ctx (args : list (ident * type)) : res (list (ident * Ctypes.type)) :=
let i := (ident_of_string "ctx") in
match args with 
| nil => OK nil
| (i, t) :: nil => 
  if eq_type t (Ptrtype (Sptype  _xdp_md_bee noattr)) 
  then OK ((ident_of_string "ctx", Tpointer (Tstruct (ident_of_string "xdp_md") noattr) noattr) :: nil)
  else OK ((i, (transBeePL_type t)) :: nil)
| _ => Error (msg "COMPILER ERROR: eBPF program should take only one argument (context)")
end.


