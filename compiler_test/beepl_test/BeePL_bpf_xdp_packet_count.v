Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

int counter = 0;

SEC("xdp")
int packet_count(void *ctx) {
    bpf_printk("%d", counter);
    counter++;
    return XDP_PASS;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";*)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _counter : ident := $"counter".
Definition _r : ident := $"r".
Definition _xdp_md : ident := $"xdp_md".
Definition _val : ident := $"val".
Definition _ctx : ident := $"ctx".
Definition _data : ident := $"data".
Definition _data_end : ident := $"data_end".
Definition _data_meta : ident := $"data_meta".
Definition _ingress_ifindex : ident := $"ingress_ifindex".
Definition _rx_queue_index : ident := $"rx_queue_index".
Definition _egress_ifindex : ident := $"egress_ifindex".
Definition _xdp_packet_count : ident := $"xdp_packet_count".
Definition _main : ident := $"main".
Definition _h : ident := $"h". (* supposed to represent heap for Reftype *)


Definition ident_to_string : list (ident * string) := ((_xdp_md, "xdp_md") ::
                                                       (_val, "val") ::
                                                       (_ctx, "ctx") ::
                                                       (_counter, "counter") ::
                                                       (_r, "r") ::
                                                       (_data, "data") ::
                                                       (_data_end, "data_end") ::
                                                       (_data_meta, "data_meta") :: 
                                                       (_ingress_ifindex, "ingress_ifindex") ::
                                                       (_rx_queue_index, "rx_queue_index") ::
                                                       (_egress_ifindex, "egress_ifindex") ::
                                                       (_xdp_packet_count, "xdp_packet_count") :: 
                                                       (_main, "main") :: nil).

Definition v_val := {|
  gvar_info := tint32u;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_counter := {|
  gvar_info := trint32u;
  gvar_init := (Init_addrof _val Ptrofs.zero :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_xdp_packet_count : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := Read mem_ident :: Write mem_ident :: nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil ;
                                   fn_vars := ((_r, tint32s) :: 
                                                nil);
                                   fn_body := Bind _r tint32s
                                                (Prim Massgn (Var _counter trint32s ::
                                                                (Prim (Bop Cop.Oadd) 
                                                                   (Prim Deref (Var _counter trint32s :: nil) tint32s ::
                                                                      cint (Int.repr 1) tint32s :: nil) tint32s) :: nil) tunit)
                                                (cint (Int.repr 2) tint32s) tint32s;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _xdp_md Struct
   (Member_plain _data tint32u :: 
    Member_plain _data_end tint32u :: 
    Member_plain _data_meta tint32u ::
    Member_plain _ingress_ifindex tint32u :: 
    Member_plain _rx_queue_index tint32u :: 
    Member_plain _egress_ifindex tint32u :: nil)
   noattr :: nil).


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_val, Gvar v_val) :: 
      (_counter, Gvar v_counter) :: 
      (_xdp_packet_count, AST.Gfun(BeePL.Internal (f_xdp_packet_count))) :: nil.

Definition public_idents : list ident := (_xdp_packet_count :: _counter :: _val :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.

(*Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_packet_count.(fn_args)) f_xdp_packet_count.(fn_vars)) empty_context f_xdp_packet_count.(fn_body)).


Compute (type_check_program example1). *) (* Type checks! *)
