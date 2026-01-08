Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx FunInd.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Linking.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers AST Maps Linking.
Require Import BeePL_aux BeePL_mem BeeTypes BeePL Globalenvs Ctypesdefs.
Require Import Coqlib Errors BeePL_values BeePL_Wrapper_Pass.

From mathcomp Require Import all_ssreflect.

Definition max_ident (x : ident) (y : ident) : ident :=
if Pos.ltb x y then y else x.

Fixpoint max_idents (xs : list ident) : ident :=
match xs with 
| nil => 1%positive
| x :: xs => max_ident x (max_idents xs)
end.

Section Max_idents.

Variable max_ident_expr : expr -> ident.

Fixpoint max_ident_exprs (es : list expr) : ident :=
match es with 
| nil => 1%positive
| e :: es => max_ident (max_ident_expr e) (max_ident_exprs es)
end.

End Max_idents.

(* Compute maximum ident used in the expression *)
Fixpoint max_ident_expr (e : expr) : ident :=
match e with 
| Val v t => 1%positive 
| Var i t => i
| Const c t => 1%positive
| App e es t => max_ident (max_ident_expr e) (max_ident_exprs max_ident_expr es)
| Prim b es t => max_ident_exprs max_ident_expr es
| Bind x t e1 e2 t' => max_ident x (max_ident (max_ident_expr e1) (max_ident_expr e2))
| Cond e1 e2 e3 t => max_ident (max_ident_expr e1) (max_ident (max_ident_expr e2) (max_ident_expr e3))
| Unit t => 1%positive
| Addr l ofs t => 1%positive
| Sinit s fs es t => max_ident s (max_ident (max_idents fs) (max_ident_exprs max_ident_expr es))
| Sfield e s t => max_ident (max_ident_expr e) s
| For e1 e2 d e3 t => max_ident (max_ident_expr e1) (max_ident (max_ident_expr e2) (max_ident_expr e3))
| Enone t => 1%positive
| Esome e t => max_ident_expr e
| Match e ps es t => max_ident (max_ident_expr e) (max_ident_exprs max_ident_expr es)
| Ebytes es t => max_ident_exprs max_ident_expr es
| Ainit a t es t' => max_ident a (max_ident_exprs max_ident_expr es)
| Aaccess a t n t' => a
end.

Definition max_ident_function (f : function) : ident :=
let fa := f.(fn_args) in
let fv := f.(fn_vars) in
let b := f.(fn_body) in 
let mf := max_ident (max_idents (unzip1 fa)) (max_idents (unzip1 fv)) in
let me := max_ident_expr b in 
max_ident mf me.

Definition max_ident_efunction (f : external_function) : ident :=
match f with 
| EF_external s bs => 1%positive
end.

Definition max_ident_fundef (f : fundef) : ident :=
match f with 
| Internal fn => max_ident_function fn 
| External fn ts t cc => max_ident_efunction fn
end.

Definition max_ident_globdef (g : globdef fundef type) : ident := 
match g with 
| Gfun fd => max_ident_fundef fd 
| Gvar v => 1%positive
end.

Fixpoint max_ident_globdefs (gs : list (globdef fundef type)) : ident := 
match gs with 
| nil => 1%positive 
| g :: gs => max_ident (max_ident_globdef g) (max_ident_globdefs gs)
end.

Definition max_ident_bmember (b : bmember) : ident :=
match b with 
| Member_plain b t => b
| Member_bitfield b sz s a z b' => b
end.

Fixpoint max_ident_bmembers (bs : list bmember) : ident :=
match bs with 
| nil => 1%positive 
| b :: bs => max_ident (max_ident_bmember b) (max_ident_bmembers bs)
end.

Definition max_ident_bc (bc : bcomposite_definition) : ident :=
match bc with 
| Bcomposite id su bs a => max_ident id (max_ident_bmembers bs)
end.

Fixpoint max_ident_bcs (bc : list bcomposite_definition) : ident :=
match bc with 
| nil => 1%positive 
| b :: bc => max_ident (max_ident_bc b) (max_ident_bcs bc)
end.

Definition max_ident_program (p : program) : ident :=
let pds := max_idents (unzip1 (unzip1 p.(prog_defs))) in 
let pgs := max_ident_globdefs (unzip2 (unzip1 p.(prog_defs))) in
let pps := max_idents p.(prog_public) in 
let pm := p.(prog_main) in 
let pbs := max_ident_bcs p.(prog_types) in 
max_idents (pds :: pgs :: pps :: pm :: pbs :: nil).

(* ------------------------------------------------------------------ *)
(* Renaming environment                                                *)
(* ------------------------------------------------------------------ *)

Definition renv := PTree.t ident.

Definition lookup_renv (ρ : renv) (x : ident) : ident :=
  match PTree.get x ρ with Some y => y | None => x end.

Definition extend (ρ : renv) (x cx : ident) : renv :=
  PTree.set x cx ρ.

Fixpoint find_string (id : ident) (tbl : list (ident * string)) : option string :=
  match tbl with
  | nil => None
  | (i, s) :: tl =>
      if Pos.eqb i id then Some s else find_string id tl
  end.

(* Fallback if not found: synthesize some name *) Locate string_of_ident.
Definition fstring_of_ident (tbl : list (ident * string)) (id : ident) : string :=
  match find_string id tbl with
  | Some s => s
  | None => "__fresh__" ++ string_of_ident id
  end.

Section Rename_exprs.

Variable rename_expr : renv -> ident -> expr -> list (ident * string) -> 
(expr * ident * list (ident * string)).

Fixpoint rename_exprs (p : renv) (next : ident) (es : list expr) (ls: list (ident * string)): 
(list expr * ident * list (ident * string)) :=
match es with 
| nil => (nil, next, ls)
| e :: es => let re := rename_expr p next e ls in 
             let res := rename_exprs p re.1.2 es re.2 in 
             (re.1.1 :: res.1.1, res.1.2, res.2)
end.

End Rename_exprs.

Fixpoint rename_expr (p : renv) (next : ident) (e : expr) (ls: list (ident * string))
: expr * ident * list (ident * string) :=
match e with 
| Val v t => (Val v t, next, ls) 
| Var i t => (Var (lookup_renv p i) t, next, ls)
| Const c t => (Const c t, next, ls)
| App e es t => let fr := rename_expr p next e ls in 
                let frs := rename_exprs rename_expr p fr.1.2 es fr.2 in 
                (App fr.1.1 frs.1.1 t, frs.1.2, frs.2)
| Prim b es t => let rs := rename_exprs rename_expr p next es ls in 
                 (Prim b rs.1.1 t, rs.1.2, rs.2)
| Bind x t e1 e2 t' => let r1 := rename_expr p next e1 ls in 
                       let next1 := r1.1.2 in
                       let x' := lookup_renv p x in
                       let s := fstring_of_ident ls x in
                       let ls' := r1.2 ++ ((x', s) :: nil) in
                       let r2 := rename_expr p next1 e2 ls' in 
                       (Bind x' t r1.1.1 r2.1.1 t', r2.1.2, r2.2)

(*let r1 := rename_expr p next e1 ls in 
                       let nx1 := r1.1.2 in 
                       let p' := extend p x nx1 in 
                       let s := fstring_of_ident ls x in 
                       let ls' := r1.2 ++ ((nx1, s) :: nil) in 
                       let nx2 := Pos.succ nx1 in 
                       let r2 := rename_expr p' nx2 e2 ls' in 
                       (Bind nx1 t r1.1.1 r2.1.1 t', r2.1.2, r2.2)*)
| Cond e1 e2 e3 t => let r1 := rename_expr p next e1 ls in 
                     let r2 := rename_expr p r1.1.2 e2 r1.2 in 
                     let r3 := rename_expr p r2.1.2 e3 r2.2 in 
                     (Cond r1.1.1 r2.1.1 r3.1.1 t, r3.1.2, r3.2)
| Unit t => (Unit t, next, ls)
| Addr l ofs t => (Addr l ofs t, next, ls)
| Sinit s fs es t => let rs := rename_exprs rename_expr p next es ls in
                     (Sinit s fs rs.1.1 t, rs.1.2, rs.2)
| Sfield e s t => let r := rename_expr p next e ls in 
                  (Sfield r.1.1 s t, r.1.2, r.2)
| For e1 e2 d e3 t => let r1 := rename_expr p next e1 ls in 
                      let r2 := rename_expr p r1.1.2 e2 r1.2 in 
                      let r3 := rename_expr p r2.1.2 e3 r2.2 in 
                      (For r1.1.1 r2.1.1 d r3.1.1 t, r3.1.2, r3.2)
| Enone t => (Enone t, next, ls)
| Esome e t => let r := rename_expr p next e ls in 
               (Esome r.1.1 t, r.1.2, r.2)
| Match e ps es t => let r := rename_expr p next e ls in 
                     let rs := rename_exprs rename_expr p r.1.2 es r.2 in 
                     (Match r.1.1 ps rs.1.1 t, rs.1.2, rs.2)
| Ebytes es t => let rs := rename_exprs rename_expr p next es ls in 
                 (Ebytes rs.1.1 t, rs.1.2, rs.2)
| Ainit a t es t' => let rs := rename_exprs rename_expr p next es ls in 
                     (Ainit a t rs.1.1 t', rs.1.2, rs.2)
| Aaccess a t n t' => (Aaccess a t n t', next, ls)
end.

(*Definition x := 2%positive.
Definition xs := (x, string_of_ident x) :: nil.
Definition dattr := {| attr_volatile := false; attr_alignas := None |}.

Definition b := Bind x Utype 
                  (Bind x Utype (Const (ConsInt (Int.repr 1)) (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                        (Var x (Vtype (BeeTypes.Tint I32 Unsigned dattr))) (Vtype (BeeTypes.Tint I32 Unsigned dattr))) 
                  (Var x (Vtype (BeeTypes.Tint I32 Unsigned dattr)))
                        (Vtype (BeeTypes.Tint I32 Unsigned dattr)). 

Compute (rename_expr (PTree.empty ident) (1%positive) b xs).*)

Fixpoint rename_idents (p : renv) (next : ident) (ids : list ident) (ls: list (ident * string)) : 
list ident * ident * renv * list (ident * string) :=
match ids with 
| nil => (nil, next, p, ls)
| id :: ids => let id' := next in 
               let p' := extend p id id' in
               let s := fstring_of_ident ls id in 
               let ls' := ls ++ ((id', s) :: nil) in 
               let ps := rename_idents p' (Pos.succ next) ids ls' in 
               (id' :: ps.1.1.1, ps.1.1.2, ps.1.2, ps.2)
end.

Definition rename_function (fn : function) (next : ident) (ls: list (ident * string)) : 
function * ident * list (ident * string) :=
let p := PTree.empty ident in 
let '(ra, n, p', ls') := rename_idents p next (unzip1 fn.(fn_args)) ls in 
let '(rv, n', p'', ls'') := rename_idents p' n (unzip1 fn.(fn_vars)) ls' in 
let '(rb, n'', ls''') := rename_expr p'' n' fn.(fn_body) ls'' in 
({| fn_return := fn.(fn_return);
   fn_effect := fn.(fn_effect);
   fn_callconv := fn.(fn_callconv) ;
   fn_args := zip ra (unzip2 fn.(fn_args));
   fn_vars := zip rv (unzip2 fn.(fn_vars));
   fn_body := rb; 
   is_ebpf := fn.(is_ebpf) |}, n'', ls''').

Definition rename_fundef (f : fundef) (next : ident) (ls: list (ident * string)) : fundef * ident * list (ident * string) :=
match f with 
| Internal fn => let '(rf, n, ls') := rename_function fn next ls in 
                 (Internal rf, n, ls')
| External fn ts t cc => (External fn ts t cc, next, ls)
end.

Definition rename_globdef (g : globdef fundef type) (next : ident) (ls: list (ident * string)) :  
globdef fundef type * ident * list (ident * string) := 
match g with 
| Gfun fd => let rg := rename_fundef fd next ls in 
             (Gfun rg.1.1, rg.1.2, rg.2)
| Gvar v => (Gvar v, next, ls)
end.

Fixpoint rename_globdefs (gs : list (globdef fundef type)) (next : ident) (ls: list (ident * string)) : 
list (globdef fundef type) * ident * list (ident * string) := 
match gs with 
| nil => (nil, next, ls)
| g :: gs => let rg := rename_globdef g next ls in 
             let rgs := rename_globdefs gs rg.1.2 rg.2 in 
             (rg.1.1 :: rgs.1.1, rgs.1.2, rgs.2)
end.

(* Max over ctx + this fundef, so locals never collide with builtin ids *)
Definition fresh_start_fundef (fd : fundef) : ident :=
  Pos.succ
    (max_ident
       (max_idents (unzip1 ident_to_string_ctx_xdp))
       (max_ident_fundef fd)).

Definition fresh_start (p : program) : ident :=
  Pos.succ (max_ident (max_idents (unzip1 ident_to_string_ctx_xdp)) (max_ident_program p)).

Definition rename_prog (p : program) : program :=
  let start  := fresh_start p in
  let ls := prog_ident_to_string p in
  let ids := unzip1 (unzip1 p.(prog_defs)) in 
  let gds := unzip2 (unzip1 p.(prog_defs)) in 
  let os := unzip2 p.(prog_defs) in 
  let '(gds', n, ls') :=
        rename_globdefs gds start ls in
  {| prog_defs := (zip (zip ids gds') os);
     prog_public := (prog_public p);
     prog_main := (prog_main p);
     prog_types := (prog_types p);
     prog_comp_env := (prog_comp_env p);
     prog_comp_env_eq := (prog_comp_env_eq p);
     prog_ident_to_string := ls' |}.








 


