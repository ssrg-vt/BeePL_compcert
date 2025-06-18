
Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* #include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("xdp")
int packet_count(struct xdp_md *ctx) {
    return XDP_PASS;
}

char LICENSE[] SEC("license") = "Dual BSD/GPL";*)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _ctx : ident := $"ctx".
Definition _xdp_packet_count : ident := $"xdp_packet_count".
Definition _main : ident := $"main".
Definition _h : ident := $"h". (* supposed to represent heap for Reftype *)


Definition ident_to_string : list (ident * string) := ident_to_string_xdp_md ++
                                                      ((_ctx, "ctx") ::
                                                       (_xdp_packet_count, "xdp_packet_count") :: 
                                                       (_main, "main") :: nil).

Definition f_xdp_packet_count : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil ;
                                   fn_vars := nil;
                                   fn_body := cint (Int.repr 2) tint32s;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (_xdp_packet_count, AST.Gfun(BeePL.Internal (f_xdp_packet_count)), Some "xdp") :: nil.

Definition public_idents : list ident := (_xdp_packet_count :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _xdp_packet_count 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_packet_count.(fn_args)) f_xdp_packet_count.(fn_vars)) empty_context f_xdp_packet_count.(fn_body)).


Compute (type_check_program example1). *) (* Type checks! *)
