
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val testbit : positive -> n -> bool

  val of_succ_nat : nat -> positive

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val sub : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> (n, n) prod

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n

  val testbit : n -> n -> bool
 end

val hd : 'a1 -> 'a1 list -> 'a1

val tl : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val pred : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val of_nat : nat -> z

  val of_N : n -> z

  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> (z, z) prod

  val quot : z -> z -> z

  val rem : z -> z -> z

  val odd : z -> bool

  val div2 : z -> z

  val log2 : z -> z

  val testbit : z -> z -> bool

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val z_lt_dec : z -> z -> sumbool

val z_le_dec : z -> z -> sumbool

val z_le_gt_dec : z -> z -> sumbool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

val shift_nat : nat -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : nat -> z

val two_power_pos : positive -> z

val two_p : z -> z

val zeq : z -> z -> sumbool

val zlt : z -> z -> sumbool

val zle : z -> z -> sumbool

val proj_sumbool : sumbool -> bool

val p_mod_two_p : positive -> nat -> z

val zshiftin : bool -> z -> z

val zzero_ext : z -> z -> z

val zsign_ext : z -> z -> z

val z_one_bits : nat -> z -> z -> z list

val p_is_power2 : positive -> bool

val z_is_power2 : z -> z option

val zsize : z -> z

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * positive
| B754_finite of bool * positive * z

type binary32 = binary_float

type binary64 = binary_float

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val of_bool : bool -> int

  val eq_dec : int -> int -> sumbool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val divs_from_divu : int -> int -> int

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val of_bool : bool -> int

  val eq_dec : int -> int -> sumbool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val divs_from_divu : int -> int -> int

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : nat
 end

module Byte :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val of_bool : bool -> int

  val eq_dec : int -> int -> sumbool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val divs_from_divu : int -> int -> int

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Int64 :
 sig
  type int = z
    (* singleton inductive, whose constructor was mkint *)
 end

module Ptrofs :
 sig
  type int = z
    (* singleton inductive, whose constructor was mkint *)
 end

module PTree :
 sig
  type 'a tree' =
  | Node001 of 'a tree'
  | Node010 of 'a
  | Node011 of 'a * 'a tree'
  | Node100 of 'a tree'
  | Node101 of 'a tree' * 'a tree'
  | Node110 of 'a tree' * 'a
  | Node111 of 'a tree' * 'a * 'a tree'

  type 'a tree =
  | Empty
  | Nodes of 'a tree'

  type 'a t = 'a tree

  val empty : 'a1 t

  val get' : positive -> 'a1 tree' -> 'a1 option

  val get : positive -> 'a1 tree -> 'a1 option

  val set0 : positive -> 'a1 -> 'a1 tree'

  val set' : positive -> 'a1 -> 'a1 tree' -> 'a1 tree'

  val set : positive -> 'a1 -> 'a1 tree -> 'a1 tree

  val map1' : ('a1 -> 'a2) -> 'a1 tree' -> 'a2 tree'

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PMap :
 sig
  type 'a t = ('a, 'a PTree.t) prod

  val init : 'a1 -> ('a1, 'a1 PTree.t) prod

  val get : positive -> 'a1 t -> 'a1

  val set : positive -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> positive

  val eq : t -> t -> sumbool
 end

module IMap :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> sumbool

  type 'x t = 'x PMap.t

  val init : 'a1 -> ('a1, 'a1 PTree.t) prod

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed :
 sig
  type t = z

  val index : z -> positive

  val eq : z -> z -> sumbool
 end

module ZMap :
 sig
  type elt = ZIndexed.t

  val elt_eq : ZIndexed.t -> ZIndexed.t -> sumbool

  type 'x t = 'x PMap.t

  val init : 'a1 -> ('a1, 'a1 PTree.t) prod

  val get : ZIndexed.t -> 'a1 t -> 'a1

  val set : ZIndexed.t -> 'a1 -> 'a1 t -> ('a1, 'a1 PTree.tree) prod

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

type errcode =
| MSG of string
| CTX of positive
| POS of positive

type errmsg = errcode list

type 'a res =
| OK of 'a
| Error of errmsg

val bind : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res

type float = binary64

type float32 = binary32

type ident = positive

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type rettype =
| Tret of typ
| Tbool
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : z option; cc_unproto : bool; cc_structret : bool }

val cc_default : calling_convention

type signature = { sig_args : typ list; sig_res : rettype; sig_cc : calling_convention }

type memory_chunk =
| Mbool
| Mint8signed
| Mint8unsigned
| Mint16signed
| Mint16unsigned
| Mint32
| Mint64
| Mfloat32
| Mfloat64
| Many32
| Many64

type init_data =
| Init_int8 of Int.int
| Init_int16 of Int.int
| Init_int32 of Int.int
| Init_int64 of Int64.int
| Init_float32 of float32
| Init_float64 of float
| Init_space of z
| Init_addrof of ident * Ptrofs.int

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list; gvar_readonly : bool; gvar_volatile : bool }

type ('f, 'v) globdef =
| Gfun of 'f
| Gvar of 'v globvar

type external_function =
| EF_external of string * signature
| EF_builtin of string * signature
| EF_runtime of string * signature
| EF_vload of memory_chunk
| EF_vstore of memory_chunk
| EF_malloc
| EF_free
| EF_memcpy of z * z
| EF_annot of positive * string * typ list
| EF_annot_val of positive * string * typ
| EF_inline_asm of string * signature * string list
| EF_debug of positive * ident * typ list

type signedness =
| Signed
| Unsigned

type intsize =
| I8
| I16
| I32
| IBool

type floatsize =
| F32
| F64

type attr = { attr_volatile : bool; attr_alignas : n option }

type type0 =
| Tvoid0
| Tint0 of intsize * signedness * attr
| Tlong0 of signedness * attr
| Tfloat0 of floatsize * attr
| Tpointer of type0 * attr
| Tarray of type0 * z * attr
| Tfunction of typelist * type0 * calling_convention
| Tstruct of ident * attr
| Tunion of ident * attr
and typelist =
| Tnil
| Tcons of type0 * typelist

type struct_or_union =
| Struct
| Union

type member =
| Member_plain of ident * type0
| Member_bitfield of ident * intsize * signedness * attr * z * bool

type members = member list

type composite_definition =
| Composite of ident * struct_or_union * members * attr

type composite = { co_su : struct_or_union; co_members : members; co_attr : attr; co_sizeof : z; co_alignof : z; co_rank : nat }

type composite_env = composite PTree.t

type bitfield =
| Full
| Bits of intsize * signedness * z * z

type 'f fundef =
| Internal of 'f
| External of external_function * typelist * type0 * calling_convention

type 'f program = { prog_defs : (ident, ('f fundef, type0) globdef) prod list; prog_public : ident list; prog_main : ident;
                    prog_types : composite_definition list; prog_comp_env : composite_env }

type block = positive

type val0 =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

type quantity =
| Q32
| Q64

type memval =
| Undef
| Byte of Byte.int
| Fragment of val0 * quantity * nat

type permission =
| Freeable
| Writable
| Readable
| Nonempty

type perm_kind =
| Max
| Cur

module Mem :
 sig
  type mem' = { mem_contents : memval ZMap.t PMap.t; mem_access : (z -> perm_kind -> permission option) PMap.t; nextblock : block }

  type mem = mem'
 end

type effect_label =
| Panic
| Divergence
| Read of ident
| Write of ident
| Alloc of ident

type effect = effect_label list

type primitive_type =
| Tunit
| Tint1 of intsize * signedness * attr
| Tlong1 of signedness * attr

type basic_type = primitive_type
  (* singleton inductive, whose constructor was Bprim *)

type type1 =
| Ptype of primitive_type
| Reftype of ident * basic_type * attr
| Ftype of type1 list * effect * type1

val transBeePL_types : (type1 -> type0 res) -> type1 list -> typelist res

val typelist_list_type : typelist -> type0 list

val transBeePL_type : type1 -> type0 res

val unzip1 : ('a1, 'a2) prod list -> 'a1 list

val unzip2 : ('a1, 'a2) prod list -> 'a2 list

val zip : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type incr_or_decr =
| Incr
| Decr

type constant =
| ConsInt of Int.int
| ConsLong of Int64.int
| ConsUnit

type vinfo = { vname : ident; vtype : type1 }

type linfo = { lname : ident; ltype : type1; lbitfield : bitfield }

type value =
| Vunit
| Vint0 of Int.int
| Vint64 of Int64.int
| Vloc of positive * Ptrofs.int

val extract_list_rvtypes : vinfo list -> (ident, type1) prod list

type builtin =
| Ref
| Deref
| Massgn
| Uop of unary_operation
| Bop of binary_operation
| Run of Mem.mem

type expr =
| Val of value * type1
| Var of vinfo
| Const of constant * type1
| App of ident option * expr * expr list * type1
| Prim of builtin * expr list * type1
| Bind of ident * type1 * expr * expr * type1
| Cond of expr * expr * expr * type1
| Unit of type1
| Addr of linfo * Ptrofs.int
| Hexpr of Mem.mem * expr * type1

val typeof_expr : expr -> type1

type function0 = { fn_return : type1; fn_callconv : calling_convention; fn_args : vinfo list; fn_vars : vinfo list; fn_body : expr }

type fundef0 =
| Internal0 of function0
| External0

type 'v globvar0 = 'v globvar

type ('f, 'v) globdef0 = ('f, 'v) globdef

type program0 = { prog_defs0 : (ident, (fundef0, type1) globdef0) prod list; prog_public0 : ident list; prog_main0 : ident;
                  prog_types0 : composite_definition list; prog_comp_env0 : composite_env }

val transBeePL_value_cvalue : value -> val0

type expr0 =
| Eval of val0 * type0
| Evar of ident * type0
| Efield of expr0 * ident * type0
| Evalof of expr0 * type0
| Ederef of expr0 * type0
| Eaddrof of expr0 * type0
| Eunop of unary_operation * expr0 * type0
| Ebinop of binary_operation * expr0 * expr0 * type0
| Ecast of expr0 * type0
| Eseqand of expr0 * expr0 * type0
| Eseqor of expr0 * expr0 * type0
| Econdition of expr0 * expr0 * expr0 * type0
| Esizeof of type0 * type0
| Ealignof of type0 * type0
| Eassign of expr0 * expr0 * type0
| Eassignop of binary_operation * expr0 * expr0 * type0 * type0
| Epostincr of incr_or_decr * expr0 * type0
| Ecomma of expr0 * expr0 * type0
| Ecall of expr0 * exprlist * type0
| Ebuiltin of external_function * typelist * exprlist * type0
| Eloc of block * Ptrofs.int * bitfield * type0
| Eparen of expr0 * type0 * type0
and exprlist =
| Enil
| Econs of expr0 * exprlist

type label = ident

type statement =
| Sskip
| Sdo of expr0
| Ssequence of statement * statement
| Sifthenelse of expr0 * statement * statement
| Swhile of expr0 * statement
| Sdowhile of expr0 * statement
| Sfor of statement * expr0 * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr0 option
| Sswitch of expr0 * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of z option * statement * labeled_statements

type function1 = { fn_return0 : type0; fn_callconv0 : calling_convention; fn_params : (ident, type0) prod list;
                   fn_vars0 : (ident, type0) prod list; fn_body0 : statement }

type fundef1 = function1 fundef

type program1 = function1 program

val transBeePL_expr_exprs : (expr -> expr0 res) -> expr list -> exprlist res

val exprlist_list_expr : exprlist -> expr0 list

val default_expr : expr0

val transBeePL_expr_expr : expr -> expr0 res

val check_var_const : expr -> bool

val transBeePL_expr_st : expr -> statement res

val transBeePL_function_function : function0 -> function1 res

val transBeePL_fundef_fundef : fundef0 -> fundef1 res

val transBeePLglobvar_globvar : type1 globvar0 -> type0 globvar res

val transBeePL_globdef_globdef : (fundef0, type1) globdef0 -> (fundef1, type0) globdef res

val transBeePL_globdefs_globdefs : (fundef0, type1) globdef0 list -> (fundef1, type0) globdef list res

val beePL_compcert : program0 -> program1 res

val apply_partial : 'a1 res -> ('a1 -> 'a2 res) -> 'a2 res

val time : string -> ('a1 -> 'a2) -> 'a1 -> 'a2

val transf_beepl_program_csyntax : program0 -> program1 res

val dattr : attr

val x : vinfo

val y : vinfo

val r : vinfo

val main : positive

val main_body : expr

val f_main : function0

val composites : composite_definition list

val global_definitions : (ident, (fundef0, type1) globdef0) prod list

val public_idents : ident list

val example1 : program0

val tcp1 : program1 res
