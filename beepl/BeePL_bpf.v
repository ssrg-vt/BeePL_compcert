Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(***** eBPF contexts ******)

Definition _pt_regs : ident := $"pt_regs".
Definition _r15 : ident := $"r15".
Definition _r14 : ident := $"r14".
Definition _r13 : ident := $"r13".
Definition _r12 : ident := $"r12".
Definition _bp : ident := $"bp".
Definition _bx : ident := $"bx".
Definition _r11 : ident := $"r11".
Definition _r10 : ident := $"r10".
Definition _r9 : ident := $"r9".
Definition _r8 : ident := $"r8".
Definition _ax : ident := $"ax".
Definition _cx : ident := $"cx".
Definition _dx : ident := $"dx".
Definition _si : ident := $"si".
Definition _di : ident := $"di".
Definition _orig_ax : ident := $"orig_ax".
Definition _ip : ident := $"ip".
Definition _cs : ident := $"cs".
Definition _flags : ident := $"flags".
Definition _sp : ident := $"sp".
Definition _ss : ident := $"ss".
Definition _ctx : ident := $"ctx".

Definition bcomposites_pt_regs : list bcomposite_definition :=
(Bcomposite _pt_regs Struct
   (Member_plain _r15 tlongu :: 
    Member_plain _r14 tlongu ::
    Member_plain _r13 tlongu ::
    Member_plain _r12 tlongu ::
    Member_plain _bp tlongu ::
    Member_plain _bx tlongu ::
    Member_plain _r11 tlongu ::
    Member_plain _r10 tlongu ::
    Member_plain _r9 tlongu ::
    Member_plain _r8 tlongu ::
    Member_plain _ax tlongu ::
    Member_plain _cx tlongu ::
    Member_plain _dx tlongu ::
    Member_plain _si tlongu ::
    Member_plain _di tlongu ::
    Member_plain _orig_ax tlongu ::
    Member_plain _ip tlongu :: 
    Member_plain _flags tlongu ::
    Member_plain _sp tlongu :: nil)
    noattr :: nil).

Definition ident_to_string_pt_regs : list (ident * string) := ((_pt_regs, "pt_regs") :: 
                                                               (_r15, "r15") ::
                                                               (_r14, "r14") ::
                                                               (_r13, "r13") ::
                                                               (_r12, "r12") ::
                                                               (_bp, "bp") ::
                                                               (_bx, "bx") ::
                                                               (_r11, "r11") ::
                                                               (_r10, "r10") ::
                                                               (_r9, "r9") ::
                                                               (_r8, "r8") ::
                                                               (_ax, "ax") ::
                                                               (_cx, "cx") ::
                                                               (_dx, "dx") ::
                                                               (_si, "si") ::
                                                               (_di, "di") ::
                                                               (_orig_ax, "orig_ax") ::
                                                               (_ip, "ip") ::
                                                               (_cs, "cs") ::
                                                               (_flags, "flags") ::
                                                               (_sp, "sp") ::
                                                               (_ss, "ss") ::
                                                               (_ctx, "ctx") :: nil).


(********************** xdp_md struct *******************************)
Definition _xdp_md : ident := $"xdp_md".
Definition _xdp_md_bee : ident := $"xdp_md_bee".
Definition _data : ident := $"data".
Definition _data_bee : ident := $"data_bee".
Definition _data_end : ident := $"data_end".
Definition _data_meta : ident := $"data_meta".
Definition _ingress_ifindex : ident := $"ingress_ifindex".
Definition _rx_queue_index : ident := $"rx_queue_index".
Definition _egress_ifindex : ident := $"egress_ifindex".


Definition ident_to_string_xdp_md : list (ident * string) := ((_xdp_md, "xdp_md") :: (_xdp_md_bee, "xdp_md_bee") :: (_data_bee, "data_bee") ::
                                                              (_data, "data") ::
                                                              (_data_end, "data_end") ::
                                                              (_data_meta, "data_meta") :: 
                                                              (_ingress_ifindex, "ingress_ifindex") ::
                                                              (_rx_queue_index, "rx_queue_index") ::
                                                              (_egress_ifindex, "egress_ifindex") :: nil).

(** xdp_md struct **)
Definition bcomposites_xdp_md : list bcomposite_definition := 
(Bcomposite _xdp_md Struct
   (Member_plain _data tint32u :: 
    Member_plain _data_end tint32u :: 
    Member_plain _data_meta tint32u ::
    Member_plain _ingress_ifindex tint32u :: 
    Member_plain _rx_queue_index tint32u :: 
    Member_plain _egress_ifindex tint32u :: nil)
   noattr :: nil).


(** BeePL xdp_md struct **)
Definition bcomposites_xdp_md_bee : list bcomposite_definition :=
(Bcomposite _xdp_md_bee Struct
   (Member_plain _data_bee Bytes :: 
    Member_plain _data_meta tint32u ::
    Member_plain _ingress_ifindex tint32u :: 
    Member_plain _rx_queue_index tint32u :: 
    Member_plain _egress_ifindex tint32u :: nil)
   noattr :: nil).


(******************** ethhdr struct ***************************)

Definition _eth_hdr : ident := $"eth_hdr".
Definition _h_dest : ident := $"h_dest".
Definition _h_source : ident := $"h_source".
Definition _h_proto : ident := $"h_proto".

Definition ident_to_string_eth_hdr : list (ident * string) := ((_eth_hdr, "eth_hdr") ::
                                                               (_h_dest, "h_dest") ::
                                                               (_h_source, "h_source") ::
                                                               (_h_proto, "h_proto") :: nil).
 
(** ethhdr struct **)
Definition bcomposites_ethhdr : list bcomposite_definition :=
(Bcomposite _eth_hdr Struct 
  (Member_plain _h_dest (tbarray tint8u 6 noattr) ::
   Member_plain _h_source (tbarray tint8u 6 noattr) ::
   Member_plain _h_proto tint16u :: nil) noattr :: nil).

(******************* BPF map struct **************************)

Definition _type : ident := $"type".
Definition _max_entries : ident := $"max_entries".
Definition _key : ident := $"key".
Definition _value : ident := $"value".
Definition _bpf_map_type_hash : ident := $"bpf_map_type_hash".


Definition ident_to_string_bpf_map_type_hash : list (ident * string) := ((_bpf_map_type_hash, "bpf_map_type_hash") ::
                                                                         (_type, "type") ::
                                                                         (_max_entries, "max_entries") ::
                                                                         (_key, "key") ::
                                                                         (_value, "value") :: nil).
 

Definition bcomposites_bpf_map_type_hash : list bcomposite_definition := (* once we support enum types these can be generalized to one def *)
(Bcomposite _bpf_map_type_hash Struct
  (Member_plain _type (Ptrtype (Reftype mem_ident (Barray pint32s 1 noattr) noattr)) ::
   Member_plain _max_entries (Ptrtype (Reftype mem_ident (Barray pint32s 5000000 noattr) noattr)) ::
   Member_plain _key trlongu ::
   Member_plain _value trlongu :: nil) noattr :: nil).

(******************* trace_entry stuct **************************)
Definition _preempt_count : ident := $"preempt_count".
Definition _pid : ident := $"pid".
Definition _trace_entry : ident := $"trace_entry".

Definition ident_to_string_trace_entry : list (ident * string) := ((_trace_entry, "trace_entry") ::
                                                                   (_type, "type") :: 
                                                                   (_flags, "flags") ::
                                                                   (_preempt_count, "preempt_count") ::
                                                                   (_pid, "pid") :: nil).

Definition bcomposites_trace_entry : list bcomposite_definition :=
(Bcomposite _trace_entry Struct 
  (Member_plain _type tint16u ::
   Member_plain _flags tint8u ::
   Member_plain _preempt_count tint8u :: 
   Member_plain _pid tint32s :: nil) noattr :: nil).

(******************* trace_event_raw_sys_enter struct *********************)
Definition _trace_event_raw_sys_enter : ident := $"trace_event_raw_sys_enter".
Definition _ent : ident := $"ent".
Definition _id : ident := $"id".
Definition _args : ident := $"args".
Definition _tdata : ident := $"__data".

Definition ident_to_string_trace_event_raw_sys_enter : list (ident * string) := 
                                                                  ((_trace_event_raw_sys_enter, "trace_event_raw_sys_enter") ::
                                                                   (_ent, "ent") :: 
                                                                   (_id, "id") ::
                                                                   (_args, "args") ::
                                                                   (_tdata, "__data") :: nil).
                                                                   

Definition bcomposites_trace_event_raw_sys_enter : list bcomposite_definition :=
(Bcomposite _trace_event_raw_sys_enter Struct 
  (Member_plain _ent (Stype _trace_entry noattr) ::
   Member_plain _id tlongs ::
   Member_plain _args (tbarray tlongu 6 noattr) :: 
   Member_plain _tdata (tbarray tint8u 0 noattr):: nil) noattr :: nil).

(********************** Helper functions *********************************)
Definition bpf_get_current_uid_gid : ident := $"bpf_get_current_uid_gid".
Definition bpf_map_lookup_elem : ident := $"bpf_map_lookup_elem".
Definition bpf_map_update_elem : ident := $"bpf_map_update_elem".
Definition bpf_get_prandom_u32 : ident := $"bpf_get_prandom_u32".
Definition bpf_get_current_pid_tgid : ident := $"bpf_get_current_pid_tgid".
Definition bpf_printk : ident := $"bpf_printk".
Definition htons : ident := $"htons".

Definition ident_to_string_hf : list (ident * string) := ((bpf_get_current_uid_gid, "bpf_get_current_uid_gid") ::
                                                          (bpf_map_lookup_elem, "bpf_map_lookup_elem") ::
                                                          (bpf_map_update_elem, "bpf_map_update_elem") ::
                                                          (bpf_get_prandom_u32, "bpf_get_prandom_u32") ::
                                                          (bpf_get_current_pid_tgid, "bpf_get_current_pid_tgid") ::
                                                          (bpf_printk, "bpf_printk") ::
                                                          (htons, "htons") :: nil).

Definition bpf_get_current_uid_gid_ef : BeePL.external_function
   := EF_external "bpf_get_current_uid_gid" 
      {| bsig_args := nil;
         bsig_ef := Io :: nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.

Definition bpf_map_lookup_elem_ef : BeePL.external_function
   := EF_external "bpf_map_lookup_elem" 
      {| bsig_args := (tostruct (ident_of_string "bpf_map_type_hash") noattr :: tolongu :: nil);
         bsig_ef := Read mem_ident :: Io :: nil;
         bsig_res := tolongu;
         bsig_cc := cc_default
      |}.

Definition bpf_map_update_elem_ef : BeePL.external_function
   := EF_external "bpf_map_update_elem" 
      {| bsig_args := (tostruct (ident_of_string "bpf_map_type_hash") noattr :: tolongu :: tolongu :: tlongu :: nil);
         bsig_ef := Write mem_ident :: Io :: nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.


Definition bpf_get_prandom_u32_ef : BeePL.external_function
   := EF_external "bpf_get_prandom_u32" 
      {| bsig_args := nil;
         bsig_ef := Io :: nil;
         bsig_res := tint32u;
         bsig_cc := cc_default
      |}.

Definition bpf_get_current_pid_tgid_ef : BeePL.external_function
   := EF_external "bpf_get_current_pid_tgid"
      {| bsig_args := nil;
         bsig_ef := Io :: nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.

Definition bpf_printk_ef : BeePL.external_function 
   := EF_external "bpf_printk"
      {| bsig_args := (trint8s :: tint32s :: nil);
         bsig_ef := Io :: nil;
         bsig_res := tint32s;
         bsig_cc := {|cc_vararg:=(Some (Z.of_nat 1)); cc_unproto:=false; cc_structret:=false|}
      |}.

(************************* External functions *******************************)
Definition htons_ef : BeePL.external_function
   := EF_external "htons" 
      {| bsig_args := tint16u :: nil;
         bsig_ef := nil;
         bsig_res := tint16u;
         bsig_cc := cc_default
      |}.
