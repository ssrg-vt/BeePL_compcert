Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx Coq.Strings.BinaryString.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Ctypes Ctyping.
Require Import BeePL_aux BeePL BeePL_values BeeTypes BeePL_mem Errors Csyntaxdefs BeePL_notations.
From mathcomp Require Import all_ssreflect. 

Local Open Scope error_monad_scope.
Local Open Scope string.

(************* External Call Type Information *******************)
(***** Map containing information about external calls *****)
Definition ef_info : Type := list type * (type * effect).

Definition ef_empty_map := PTree.empty ef_info.

Definition ef_env : Type := PTree.t ef_info.

Notation "m [ a <- b ]" := (PTree.set (ident_of_string a) b m) (at level 10, left associativity).
Notation "m [ a ]" := (PTree.get (ident_of_string a) m) (at level 10, left associativity).

(* Add all external functions needed for BeePL *)
Definition  beepl_ef_env : ef_env :=
ef_empty_map ["bpf_get_prandom_u32" <- (nil, (tint32u, (Io :: nil)))]
             ["bpf_ktime_get_ns" <- (nil, (tlongu, (Io :: nil)))]
             ["add" <- ((tint32s :: trint32s :: nil), (tint32s, nil))]
             ["bpf_get_current_uid_gid" <- (nil, (tlongu, (Io :: nil)))]
             ["bpf_map_lookup_elem" <- ((tostruct (ident_of_string "bpf_map_type_hash") noattr :: tolongu :: nil), 
                                            (tolongu, (Read :: Io :: nil)))]
             ["bpf_map_update_elem" <- ((tostruct (ident_of_string "bpf_map_type_hash") noattr :: tolongu :: tolongu :: tlongu :: nil), 
                                           (tlongu, (Write :: Io :: nil)))]
             ["bpf_printk" <- ((trint8s :: tint32s :: nil), (tint32s, (Io :: nil)))]
             ["bpf_probe_read_kernel" <- ((tolongu :: tint32u :: tolongu :: nil), (tlongu, (Read :: Io :: nil)))]
             ["bpf_get_current_comm" <- ((tolongu :: tint32u :: nil),
                            (tlongu, (Read :: Io :: nil)))]
             ["bpf_probe_read_user_str" <- ((tolongu :: tint32u :: tolongu :: nil),
                               (tlongu, (Read :: Io :: nil)))].

             
Definition get_ef_type (efenv : ef_env) (s : string) : res ef_info :=
match efenv[s] with 
| Some t => OK t
| None => Error (msg "TYPE ERROR: The type signature of external function is not present in ef_env")
end.

(* Add more pairs for sec attributes and function arguments *)
Definition check_type_attr (t : type) (s : string) : bool :=
let id1 := ident_of_string "xdp" in
let id2 := ident_of_string "__sk_buff" in 
let id3 := ident_of_string "pt_regs" in
match t, s with 
| Ptrtype (Reftype (Bstruct id1 _) _), "xdp" => true 
| (Stype id1 _), "xdp" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "socket" => true 
| (Stype id2 _), "socket" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "tc" => true 
| (Stype id2 _), "tc" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "cls" => true 
| (Stype id2 _), "cls" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "act" => true 
| (Stype id2 _), "act" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "cgroup/ingress" => true 
| (Stype id2 _), "cgroup/ingress" => true 
| Ptrtype (Reftype (Bstruct id2 _) _), "cgroup/skb" => true 
| (Stype id2 _), "cgroup/skb" => true 
| Ptrtype (Reftype (Bstruct id3 _) _), "kretprobe/do_sys_open" => true 
| (Stype id3 _), "kretprobe/do_sys_open" => true 

| _, _ => false
end.

Fixpoint check_type_attrs (ts : list type) (s : string) : bool :=
match ts with 
| nil => true 
| t :: ts' => check_type_attr t s && check_type_attrs ts' s
end.


Fixpoint check_get_fundef_sec (pds : list (ident * BeePL.globdef BeePL.fundef BeeTypes.type * option string)) : bool :=
match pds with 
| nil => true 
| pd :: pds => match pd.1.2 with 
               | AST.Gfun f => match f with 
                               | Internal f => if f.(is_ebpf) 
                                               then let ts := unzip2 f.(fn_args) in
                                                    match pd.2 with 
                                                    | Some s => check_type_attrs ts s && check_get_fundef_sec pds
                                                    | None => check_get_fundef_sec pds
                                                    end
                                               else true 
                               | _ => true 
                               end
               | _ => check_get_fundef_sec pds (* fix it later to also check for global variable related to map creation *)
               end
     
end.


