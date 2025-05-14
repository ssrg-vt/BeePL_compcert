Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct BeePL_Check_Reserved_Struct.

Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.

(* Missing list of public functions *) 
Fixpoint wrapper_beepl_struct_ebpf_struct (cs : list composite_definition) : list composite_definition :=
match cs with 
| nil => nil
| c1 :: cs1 => match c1 with 
               | (Composite _xdp_md_bee Struct
                   (Ctypes.Member_plain _data (Tstruct bytes_t {| attr_volatile := false; attr_alignas := None |}) :: rest) 
                   {| attr_volatile := false; attr_alignas := None |})
                   => (Composite (ident_of_string "xdp_md") Struct
                        (Ctypes.Member_plain _data (Ctypes.Tint I32 Unsigned noattr)  :: 
                         Ctypes.Member_plain (ident_of_string "data_end") (Ctypes.Tint I32 Unsigned noattr)  :: rest) noattr) :: c1 ::
                      (*(Composite (ident_of_string "xdp_md_wrapper") Struct
                        (Ctypes.Member_plain (ident_of_string "start") (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr) :: 
                         Ctypes.Member_plain (ident_of_string "end")  (Ctypes.Tpointer (Ctypes.Tint I8 Unsigned noattr) noattr) :: rest) noattr) ::*)
                       wrapper_beepl_struct_ebpf_struct cs1
              | _ => c1 :: wrapper_beepl_struct_ebpf_struct cs1
              end
end.
