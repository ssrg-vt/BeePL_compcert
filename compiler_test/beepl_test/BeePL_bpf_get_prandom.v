Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker. 
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

int main() {
   struct xdp_md *x;
   xdp_prog(x);
}

char _license[] SEC("license") = "GPL";
}*)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _rand : ident := $"rand".
Definition _bpf_get_prandom_u32 : ident := $"bpf_get_prandom_u32".
Definition _xdp_md : ident := $"xdp_md".
Definition _ctx : ident := $"ctx".
Definition _data : ident := $"data".
Definition _data_end : ident := $"data_end".
Definition _data_meta : ident := $"data_meta".
Definition _ingress_ifindex : ident := $"ingress_ifindex".
Definition _rx_queue_index : ident := $"rx_queue_index".
Definition _egress_ifindex : ident := $"egress_ifindex".
Definition _xdp_prog : ident := $"xdp_prog".
Definition _x : ident := $"x".
Definition _bpf_random := $"bpf_random".
Definition _main : ident := $"main".
Definition _h : ident := $"h". (* supposed to represent heap for Reftype *)


Definition ident_to_string : list (ident * string) := ((_xdp_md, "xdp_md") ::
                                                       (_ctx, "ctx") ::
                                                       (_rand, "rand") :: 
                                                       (_bpf_get_prandom_u32, "bpf_get_prandom_u32") :: 
                                                       (_data, "data") ::
                                                       (_data_end, "data_end") ::
                                                       (_data_meta, "data_meta") :: 
                                                       (_ingress_ifindex, "ingress_ifindex") ::
                                                       (_rx_queue_index, "rx_queue_index") ::
                                                       (_egress_ifindex, "egress_ifindex") ::
                                                       (_xdp_prog, "xdp_prog") :: 
                                                       (_x, "x") ::
                                                       (_main, "main") :: nil).

Definition bpf_external_function : BeePL.external_function
   := EF_external "bpf_get_prandom_u32" 
      {| bsig_args := nil;
         bsig_ef := nil;
         bsig_res := Ptype (BeeTypes.Tint I32 Unsigned dattr);
         bsig_cc := cc_default
      |}.

Definition f_xdp_prog : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, Reftype _h (BeeTypes.Bstruct _xdp_md dattr) dattr) :: nil ;
                                   fn_vars := ((_rand, BeeTypes.Ptype (BeeTypes.Tint I32 Ctypes.Unsigned dattr)) :: 
                                                nil);
                                   fn_body := Bind 
                                                (_rand) 
                                                (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                                (Eapp bpf_external_function nil nil (Ptype (BeeTypes.Tint I32 Unsigned dattr))) 
                                                (Const (ConsInt (Int.repr 1)) (Ptype (BeeTypes.Tint I32 Unsigned dattr)))
                                             (Ptype (BeeTypes.Tint I32 Unsigned dattr))|}.

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _xdp_md Struct
   (Member_plain _data (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
    Member_plain _data_end (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
    Member_plain _data_meta (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) ::
    Member_plain _ingress_ifindex (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
    Member_plain _rx_queue_index (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: 
    Member_plain _egress_ifindex (BeeTypes.Ptype (BeeTypes.Tint Ctypes.I32 Ctypes.Unsigned dattr)) :: nil)
   noattr :: nil).


Definition f_main : BeePL.function := {| 
                                   fn_return := (Ptype (BeeTypes.Tint I32 Unsigned dattr));
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := nil;
                                   fn_vars := (_x, Reftype _h (BeeTypes.Bstruct _xdp_md dattr) dattr) :: nil;
                                   fn_body := (App (Var _xdp_prog (Ftype ((Reftype _h (BeeTypes.Bstruct _xdp_md dattr) dattr) :: nil) 
                                                                           nil 
                                                                      (Ptype (BeeTypes.Tint I32 Unsigned dattr)))) 
                                                  (Var _x (Reftype _h (BeeTypes.Bstruct _xdp_md dattr) dattr) :: nil) 
                                                  (Ptype (BeeTypes.Tint I32 Unsigned dattr))) |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_bpf_get_prandom_u32, AST.Gfun(BeePL.External (bpf_external_function)
                                     nil
                                     (Ptype (BeeTypes.Tint I32 Unsigned dattr))
                                     (cc_default))) :: 
      (_xdp_prog, AST.Gfun(BeePL.Internal (f_xdp_prog))) ::
      (_main, AST.Gfun(BeePL.Internal (f_main))) :: nil.

Definition public_idents : list ident := (_main :: _xdp_prog :: nil).

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
                                                   ident_to_string.*)


(*Compute (type_check_program example1).*) (* Type checks *)
