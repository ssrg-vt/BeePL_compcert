Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf BeePL_Bytes_Struct BeePL_aux BeePL_Csyntax Maps.
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(* 
#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <linux/if_ether.h>
#include <arpa/inet.h>


SEC("xdp_drop")
int xdp_drop_prog(struct xdp_md *ctx)
{
    void star data_end = (void star)(long)ctx->data_end;
    void star data = (void star)(long)ctx->data;
    struct ethhdr *eth = data;
    __u16 h_proto;

    if (data + sizeof(struct ethhdr) > data_end)
        return XDP_DROP;

    h_proto = eth->h_proto;

    if (h_proto == htons(ETH_P_IPV6))
        return XDP_DROP;

    return XDP_PASS;
}

char _license[] SEC("license") = "GPL"; *)

Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _eth : ident := $"eth".
Definition _hproto : ident := $"hproto".
Definition _ctx : ident := $"ctx".
Definition _xdp_drop_prog : ident := $"xdp_drop_prog".

Definition ident_to_string : list (ident * string) := ident_to_string_xdp_md ++ ident_to_string_eth_hdr ++ ident_to_string_hf ++ ident_to_string_bytes ++
                                                      ((_ctx, "ctx") ::
                                                       (_eth, "eth") ::
                                                       (_hproto, "hproto") ::
                                                       (_xdp_drop_prog, "xdp_drop_prog") :: nil).

Definition f_xdp_drop_prog : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md_bee) :: nil ;
                                   fn_vars := (_eth, Stype _eth_hdr noattr) :: (_data_bee, Bytes) :: (_hproto, tint16u) :: nil;
                                   fn_body := Match (Sfield (Var _ctx (tpstruct _xdp_md_bee)) _data_bee Bytes)  
                                                    (Pbytes _eth (Stype _eth_hdr noattr) ((_h_proto, tint16u) :: nil) :: nil)  
                                                     (Bind _hproto tint16u 
                                                         (Sfield (Var _eth (Stype _eth_hdr noattr)) _h_proto tint16u) 
                                                         (Cond (Prim (Bop Cop.Oeq) (Var _hproto tint16u :: 
                                                                                    App (Var htons (tfun (tint16u :: nil) nil tint16u)) 
                                                                                        (Prim (Bop (Cop.Oand)) 
                                                                                                      (cint (Int.repr 0x86DD) tint32s ::  
                                                                                                       cint (Int.repr 65535) tint32s :: nil) tint16u :: nil) tint16u :: nil) 
                                                                                   tint32s)
                                                               (cint (Int.repr 1) tint32s) 
                                                               (cint (Int.repr 2) tint32s) tint32s) tint32s ::
                                                      cint (Int.repr 1) tint32s :: nil) tint32s;
                                   is_ebpf := true |}.


Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md_bee ++ bcomposites_ethhdr.

Definition global_definitions : list (ident * AST.globdef BeePL.fundef type * option string) 
   := (htons, AST.Gfun(BeePL.External (htons_ef) (tint16u :: nil) tint16u cc_default), None) ::
      (_xdp_drop_prog, AST.Gfun(BeePL.Internal (f_xdp_drop_prog)), None) :: nil.

Definition public_idents : list ident := (_xdp_drop_prog :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _xdp_drop_prog
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_xdp_drop_prog.(fn_args)) 
                         f_xdp_drop_prog.(fn_vars)) empty_context f_xdp_drop_prog.(fn_body)).

Compute (type_check_program example1). *) (* After having lexer and parser, type checker should work *)


