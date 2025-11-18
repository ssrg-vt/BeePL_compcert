Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Coqlib SimplExpr Csyntaxdefs BeePL_notations Csyntaxdefs.
Require Import BeePL_aux BeePL BeeTypes Csyntax Errors SimplExpr BeePL_values DecimalString BeePL_Bytes_Struct BeePL_Check_Reserved_Struct.

Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope string_scope.
Local Open Scope gensym_monad_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* ---------------------------------------------------------------------- *)
(*  Idents for ctx / xdp_md / fields                                      *)
(* ---------------------------------------------------------------------- *)

(* These should normally live with your other global idents,
   or in Csyntaxdefs-style files, and be added to ident_to_string. *)

Definition _xdp_md_bee : ident := $"_xdp_md_bee".
Definition _data_bee   : ident := $"_data_bee".

Definition _ctx        : ident := $"ctx".

Definition _xdp_md     : ident := $"xdp_md".
Definition _data       : ident := $"_data".
Definition _data_end   : ident := $"_data_end".
Definition _data_meta   : ident := $"_data_meta".
Definition _ingress_ifindex  : ident := $"_ingress_ifindex".
Definition _rx_queue_index  : ident := $"_rx_queue_index".
Definition _egress_ifindex  : ident := $"_egress_ifindex".

(* Local mapping of idents to strings that we always want exported *)
Definition ident_to_string_ctx_xdp : list (ident * string) := 
  (_ctx,        "ctx")
  :: (_xdp_md,    "xdp_md")
  :: (_data,      "_data")
  :: (_data_end,  "_data_end")
  :: (_data_meta, "_data_meta")
  :: (_ingress_ifindex, "_ingress_ifindex")
  :: (_rx_queue_index, "_rx_queue_index")
  :: (_egress_ifindex, "_egress_ifindex")
  :: (_xdp_md_bee,"_xdp_md_bee")
  :: (_data_bee,  "_data_bee") :: nil
  ++ ident_to_string_bytes.


(* A concrete C composite for the real eBPF xdp_md context *)
Definition xdp_md_ccomposite : composite_definition :=
  Composite _xdp_md Struct
    (  Ctypes.Member_plain _data       (Ctypes.Tint I32 Unsigned noattr)
    :: Ctypes.Member_plain _data_end  (Ctypes.Tint I32 Unsigned noattr)
    :: Ctypes.Member_plain _data_meta (Ctypes.Tint I32 Unsigned noattr)
    :: Ctypes.Member_plain _ingress_ifindex (Ctypes.Tint I32 Unsigned noattr)
    :: Ctypes.Member_plain _rx_queue_index  (Ctypes.Tint I32 Unsigned noattr)
    :: Ctypes.Member_plain _egress_ifindex  (Ctypes.Tint I32 Unsigned noattr)
    :: nil)
    noattr.

(* ---------------------------------------------------------------------- *)
(*  Utilities on composites                                               *)
(* ---------------------------------------------------------------------- *)

Definition get_struct_name (c : composite_definition) : ident :=
  match c with
  | Composite s _ _ _ => s
  end.

Definition check_member_name (m : member) : bool :=
  match m with
  | Ctypes.Member_plain mn _ =>
      if ident_eq mn _data_bee then true else false
  | Ctypes.Member_bitfield mn _ _ _ _ _ =>
      if ident_eq mn _data_bee then true else false
  end.

(* Replace the [_data_bee : bytes] field by
     data      : unsigned int
     data_end  : unsigned int
   in the members list, **only for the xdp_md struct we generate**. *)
Fixpoint transform_bytes_data_data_end (ms : members) : members :=
  match ms with
  | nil => nil
  | m :: ms1 =>
      if check_member_name m
      then
        Ctypes.Member_plain _data     (Ctypes.Tint I32 Unsigned noattr)
      :: Ctypes.Member_plain _data_end (Ctypes.Tint I32 Unsigned noattr)
      :: transform_bytes_data_data_end ms1
      else
        m :: transform_bytes_data_data_end ms1
  end.

(* Given the BeePL struct [_xdp_md_bee], generate a **new** eBPF struct
   [struct xdp_md { data; data_end; ... }] but keep the original _xdp_md_bee. *)
(*Definition transform_struct_bee_decl_ebpf_decl
           (c : composite_definition)
  : list composite_definition :=
  match c with
  | Composite s su m a =>
      if ident_eq s _xdp_md_bee
      then
        (* New eBPF view of the context: struct xdp_md { data; data_end; ... } *)
        Composite _xdp_md Struct (transform_bytes_data_data_end m) a
        :: c :: nil
      else
        c :: nil
  end.*)

Fixpoint wrapper_beepl_struct_ebpf_struct
         (cs : list composite_definition) : list composite_definition := cs.
  (*match cs with
  | nil => nil
  | c1 :: cs1 =>
      transform_struct_bee_decl_ebpf_decl c1
      ++ wrapper_beepl_struct_ebpf_struct cs1
  end.*)

(* ---------------------------------------------------------------------- *)
(*  Transform ctx argument type from BeePL _xdp_md_bee* to eBPF xdp_md*   *)
(* ---------------------------------------------------------------------- *)

Definition transform_ctx_ebpf_ctx
           (args : list (ident * type))
  : res (list (ident * Ctypes.type)) :=
  (* For eBPF functions, we force the C signature to be:
       int foo(struct xdp_md *ctx);
     regardless of the BeePL type we saw. *)
  match args with
  | (arg_id, _t) :: nil =>
      (* Ignore BeePL's type, standardize on xdp_md *ctx *)
      OK (( _ctx
          , Tpointer (Tstruct _xdp_md noattr) noattr
          ) :: nil)
  | nil =>
      Error (msg "COMPILER ERROR: eBPF program must take exactly one argument (context)")
  | _ :: _ :: _ =>
      Error (msg "COMPILER ERROR: eBPF program should take only one argument (context)")
  end.



(*Definition get_struct_name (c : composite_definition) : ident :=
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
end.*)


