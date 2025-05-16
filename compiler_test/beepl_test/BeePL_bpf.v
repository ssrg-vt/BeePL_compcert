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

Definition _xdp_md : ident := $"xdp_md".
Definition _data : ident := $"data".
Definition _data_end : ident := $"data_end".
Definition _data_meta : ident := $"data_meta".
Definition _ingress_ifindex : ident := $"ingress_ifindex".
Definition _rx_queue_index : ident := $"rx_queue_index".
Definition _egress_ifindex : ident := $"egress_ifindex".


Definition ident_to_string_xdp_md : list (ident * string) := ((_xdp_md, "xdp_md") ::
                                                              (_data, "data") ::
                                                              (_data_end, "data_end") ::
                                                              (_data_meta, "data_meta") :: 
                                                              (_ingress_ifindex, "ingress_ifindex") ::
                                                              (_rx_queue_index, "rx_queue_index") ::
                                                              (_egress_ifindex, "egress_ifindex") :: nil).

Definition bcomposites_xdp_md : list bcomposite_definition := 
(Bcomposite _xdp_md Struct
   (Member_plain _data tint32u :: 
    Member_plain _data_end tint32u :: 
    Member_plain _data_meta tint32u ::
    Member_plain _ingress_ifindex tint32u :: 
    Member_plain _rx_queue_index tint32u :: 
    Member_plain _egress_ifindex tint32u :: nil)
   noattr :: nil).



(**** Helper functions ****)
Definition bpf_get_current_uid_gid : BeePL.external_function
   := EF_external "bpf_get_current_uid_gid" 
      {| bsig_args := nil;
         bsig_ef := nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.

Definition bpf_map_lookup_elem : BeePL.external_function
   := EF_external "bpf_map_lookup_elem" 
      {| bsig_args := (tostruct (ident_of_string "bpf_map") noattr :: tolongu :: nil);
         bsig_ef := nil;
         bsig_res := tolongu;
         bsig_cc := cc_default
      |}.

Definition bpf_map_update_elem : BeePL.external_function
   := EF_external "bpf_map_update_elem" 
      {| bsig_args := (tostruct (ident_of_string "bpf_map") noattr :: trlongu :: trlongu :: tlongu :: nil);
         bsig_ef := nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.


Definition bpf_get_prandom_u32 : BeePL.external_function
   := EF_external "bpf_get_prandom_u32" 
      {| bsig_args := nil;
         bsig_ef := nil;
         bsig_res := tint32u;
         bsig_cc := cc_default
      |}.
