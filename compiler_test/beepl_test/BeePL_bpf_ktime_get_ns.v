Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>

SEC("kprobe/sys_execve")
int bpf_prog(struct pt_regs *ctx) {
    __u64 ts = bpf_ktime_get_ns();  // helper function: no string involved
    // Do something with ts; here, we just return the lower 32 bits
    return (int)(ts & 0xFFFFFFFF);
}

char LICENSE[] SEC("license") = "GPL"; *)


Definition dattr := {| attr_volatile := false; attr_alignas := None |}.
Definition _bpf_ktime_get_ns : ident := $"bpf_ktime_get_ns".
Definition _pt_regs : ident := $"pt_regs".
Definition _ctx : ident := $"ctx".
Definition _ebx : ident := $"ebx".
Definition _ecx : ident := $"ecx".
Definition _edx : ident := $"edx".
Definition _esi : ident := $"esi".
Definition _edi : ident := $"edi".
Definition _ebp : ident := $"ebp".
Definition _eax : ident := $"eax".
Definition _xds : ident := $"xds".
Definition _xes : ident := $"xes".
Definition _xfs : ident := $"xfs".
Definition _xgs : ident := $"xgs".
Definition _orig_eax : ident := $"orig_eax".
Definition _eip : ident := $"eip".
Definition _xcs : ident := $"xcs".
Definition _eflags : ident := $"eflags".
Definition _esp : ident := $"esp".
Definition _xss : ident := $"xss".
Definition _bpf_prog : ident := $"bpf_prog".
Definition _ts : ident := $"ts".
Definition _main : ident := $"main".

Definition ident_to_string : list (ident * string) := ((_pt_regs, "pt_regs") ::
                                                       (_ctx, "ctx") ::
                                                       (_bpf_ktime_get_ns, "bpf_ktime_get_ns") :: 
                                                       (_ebx, "ebx") ::
                                                       (_ecx, "ecx") ::
                                                       (_edx, "edx") :: 
                                                       (_esi, "esi") ::
                                                       (_edi, "edi") ::
                                                       (_ebp, "ebp") ::
                                                       (_eax, "eax") ::
                                                       (_xds, "xds") ::
                                                       (_xes, "xes") ::
                                                       (_xfs, "xfs") ::
                                                       (_xgs, "xgs") ::
                                                       (_orig_eax, "ebp") ::
                                                       (_eip, "ebp") ::
                                                       (_xcs, "xcs") ::
                                                       (_eflags, "eflags") ::
                                                       (_esp, "esp") ::
                                                       (_xss, "xss") ::
                                                       (_bpf_prog, "bpf_prog") :: 
                                                       (_ts, "ts") ::
                                                       (_main, "main") :: nil).

Definition bpf_external_function : BeePL.external_function
   := EF_external "bpf_ktime_get_ns" 
      {| bsig_args := nil;
         bsig_ef := nil;
         bsig_res := tlongu;
         bsig_cc := cc_default
      |}.

Definition f_bpf_prog : BeePL.function := {| 
                                   fn_return := tlongu;
                                   fn_effect := nil;
                                   fn_callconv := cc_default;
                                   fn_args := (_ctx, Reftype mem_ident (BeeTypes.Bstruct _pt_regs dattr) dattr) :: nil ;
                                   fn_vars := ((_ts, tlongu) :: 
                                                nil);
                                   fn_body := Bind 
                                                (_ts) tlongu
                                                (App (Var _bpf_ktime_get_ns (tfun nil nil tlongu)) nil tlongu)
                                                (Prim (Bop Cop.Oand) (Var _ts tlongu :: clong (Int64.repr 0xFFFFFFFF) tlongu :: nil) tlongu)
                                              tlongu|}.

Definition bcomposites : list bcomposite_definition :=
(Bcomposite _pt_regs Struct
   (Member_plain _ebx tlongs :: 
    Member_plain _ecx tlongs ::
    Member_plain _edx tlongs ::
    Member_plain _esi tlongs ::
    Member_plain _edi tlongs ::
    Member_plain _ebp tlongs ::
    Member_plain _eax tlongs ::
    Member_plain _xds tint32s ::
    Member_plain _xes tint32s ::
    Member_plain _xfs tint32s ::
    Member_plain _xgs tint32s ::
    Member_plain _orig_eax tlongs ::
    Member_plain _eip tlongs ::
    Member_plain _xcs tint32s ::
    Member_plain _eflags tlongs ::
    Member_plain _esp tlongs ::
    Member_plain _xss tint32s :: nil)
    noattr :: nil).


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_bpf_ktime_get_ns, AST.Gfun(BeePL.External (bpf_external_function)
                                     nil tlongu (cc_default))) :: 
      (_bpf_prog, AST.Gfun(BeePL.Internal (f_bpf_prog))) :: nil.

Definition public_idents : list ident := (_bpf_prog :: nil).

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


Compute (type_check_program example1).*) (* Type checks *)
