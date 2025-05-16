Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*#include <linux/bpf.h>
#include "bpf_helpers.h"

SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
    // Call a helper to get a pseudo-random number
    __u32 rand = bpf_get_prandom_u32();

    // Always pass the packet (simplest behavior)
    return XDP_PASS;
}

char _license[] SEC("license") = "GPL";
}*)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _rand : ident := $"rand".
Definition _bpf_get_prandom_u32 : ident := $"bpf_get_prandom_u32".
Definition _ctx : ident := $"ctx".
Definition _xdp_prog : ident := $"xdp_prog".
Definition _x : ident := $"x".
Definition _bpf_random := $"bpf_random".
Definition _main : ident := $"main".
Definition _h : ident := $"h". (* supposed to represent heap for Reftype *)


Definition ident_to_string : list (ident * string) := ident_to_string_xdp_md ++ 
                                                      ((_ctx, "ctx") ::
                                                       (_rand, "rand") :: 
                                                       (_bpf_get_prandom_u32, "bpf_get_prandom_u32") :: 
                                                       (_xdp_prog, "xdp_prog") :: 
                                                       (_x, "x") ::
                                                       (_main, "main") :: nil).

Definition f_xdp_prog : BeePL.function := {| 
                                   fn_return := tint32s;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, tpstruct _xdp_md) :: nil ;
                                   fn_vars := ((_rand, tint32s) :: 
                                                nil);
                                   fn_body := Bind 
                                                (_rand) tint32u
                                                (App (Var _bpf_get_prandom_u32 (tfun nil nil tint32u)) nil tint32u)
                                                (cint (Int.repr 2) tint32s) tint32s;
                                   is_ebpf := true |}.

Definition bcomposites : list bcomposite_definition := bcomposites_xdp_md.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_bpf_get_prandom_u32, AST.Gfun(BeePL.External bpf_get_prandom_u32
                                     nil tint32u
                                     (cc_default))) :: 
      (_xdp_prog, AST.Gfun(BeePL.Internal (f_xdp_prog))) :: nil.

Definition public_idents : list ident := (_xdp_prog :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _main 
                                                   bcomposite_correct
                                                   ident_to_string.


Compute (type_check_program example1). *) (* Type checks *)
