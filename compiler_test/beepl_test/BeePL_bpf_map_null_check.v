Require Import Integers AST Ctypes BeePL BeeTypes BeePL_values BeePL_typechecker BeePL_notations BeePL_bpf. 
From Coq Require Import String ZArith.
From compcert Require Import Csyntaxdefs.
Import Csyntaxdefs.CsyntaxNotations.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope csyntax_scope.

(*#include <linux/bpf.h>
#include <bpf/bpf_helpers.h>
#include <stdint.h>
#include <stdlib.h>
#include <memory.h>

// How many times each different user has run programs.

struct {
    __uint(type, BPF_MAP_TYPE_HASH);
    __uint(max_entries, 5000000);
    __type(key, uint64_t);
    __type(value, uint64_t);
} counter_table SEC(".maps");

SEC("ksyscall/execve")

int hello(void *ctx) {
     uint64_t uid; (* alloc *)
     uint64_t *p; 
    

     uid = bpf_get_current_uid_gid() & 0xFFFFFFFF;   //returns a 64 bits integer containing the current GID and UID (* io, write *)
                                                    //gets the user id that is running the process that trigegered this krpobe event. 
                                                    //user-id is held in lowest 32 bits of the 64-bit value that gets returned. (top 32 holds the group id)
     p = bpf_map_lookup_elem(&counter_table, (&uid)); //returns a pointer to the corresponding value in the hash table (* read; io *)
     return (int)!p
}*)
Definition _val : ident := $"val".
Definition _counter_table : ident := $"counter_table".
Definition _uid : ident := $"uid".
Definition _tuid : ident := $"tuid".
Definition _p : ident := $"p".
Definition _p1 : ident := $"p1".
Definition _r : ident := $"r".
Definition _ctx : ident := $"ctx".
Definition _hash_map_example : ident := $"hash_map_example".

Definition ident_to_string : list (ident * string) := ident_to_string_bpf_map_type_hash ++ ident_to_string_pt_regs ++ ident_to_string_hf ++
                                                      ((_val, "val") ::
                                                       (_counter_table, "counter_table") ::
                                                       (_uid, "uid") ::
                                                       (_tuid, "tuid") ::
                                                       (_p, "p") :: (_p1, "p1") ::
                                                       (_r, "r") ::
                                                       (_ctx, "ctx") ::
                                                       (_hash_map_example, "hash_map_example") :: nil).
                                                 

Definition v_val := {|
  gvar_info := Stype _bpf_map_type_hash noattr;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_counter_table := {|
  gvar_info := (tostruct _bpf_map_type_hash noattr);
  gvar_init := (Init_addrof _val Ptrofs.zero :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition bcomposites : list bcomposite_definition := bcomposites_pt_regs ++ bcomposites_bpf_map_type_hash.

Definition f_hash_map_example : BeePL.function := {| 
  fn_return := tint32s;
  fn_effect := Alloc mem_ident :: Io :: Write mem_ident :: Read mem_ident :: Io :: 
               Read mem_ident :: nil;
  fn_callconv := cc_default;
  fn_args := (_ctx, tpstruct _pt_regs) :: nil ;
  fn_vars := ((_uid, trlongu) :: (_p, tolongu) :: (_p1, trlongu) :: nil); 
  fn_body := Bind (_uid) trlongu
               (Prim Ref (clong (Int64.repr 0) tlongu :: nil) (trlongu))
                (Bind (_r) trlongu
                  (Prim Massgn (Var (_uid) trlongu ::
                                Prim (Bop Cop.Oand) 
                                     (App (Var bpf_get_current_uid_gid (tfun nil (Io :: nil) tlongu)) nil tlongu ::
                                        clong (Int64.repr 4294967295) tlongu :: nil) tlongu :: nil) tunit)
                         (Bind _p tolongu 
                            (App (Var bpf_map_lookup_elem 
                                        (tfun (tostruct _bpf_map_type_hash noattr :: tolongu :: nil) (Read mem_ident :: Io :: nil) tolongu)) 
                                        (Var _counter_table (tostruct _bpf_map_type_hash noattr) ::
                                         Var _uid trlongu :: nil) tolongu)
                            (Prim (Cast tint32u) (Prim Deref (Var _p tolongu :: nil) tlongu :: nil) tint32u) tint32u) tint32u) tint32u;
                                        
                                                    
  is_ebpf := true |}.


Definition global_definitions : list (ident * AST.globdef BeePL.fundef type) 
   := (_counter_table, Gvar v_counter_table) :: (_val, Gvar v_val) :: 
      (bpf_get_current_uid_gid, AST.Gfun(BeePL.External (bpf_get_current_uid_gid_ef)
                                     nil tlongu
                                     (cc_default))) ::
      (bpf_map_lookup_elem, AST.Gfun(BeePL.External (bpf_map_lookup_elem_ef)
                                     (tostruct _bpf_map_type_hash noattr :: tolongu :: nil) tolongu
                                     (cc_default))) ::
      (bpf_map_update_elem, AST.Gfun(BeePL.External (bpf_map_update_elem_ef)
                                     (tostruct _bpf_map_type_hash noattr :: tolongu :: tolongu :: tlongu :: nil) tlongu
                                     (cc_default))) ::
      (_hash_map_example, AST.Gfun(BeePL.Internal (f_hash_map_example))) :: nil.

Definition public_idents : list ident := (_hash_map_example :: nil).

Lemma bcomposite_correct :
  wf_bcomposites bcomposites.
Proof.
  unfold wf_bcomposites.
  unfold build_bcomposite_env; simpl; constructor. 
Qed.

(*Definition example1 : BeePL.program := @mkbprogram bcomposites 
                                                   global_definitions 
                                                   public_idents 
                                                   _hash_map_example 
                                                   bcomposite_correct
                                                   ident_to_string.

Compute (type_check_expr example1.(prog_comp_env) 
                         (bind_vars (bind_vars empty_context f_hash_map_example.(fn_args)) 
                         f_hash_map_example.(fn_vars)) empty_context f_hash_map_example.(fn_body)).

Compute (type_check_program example1). *)  (* Does not type checks! *) 
