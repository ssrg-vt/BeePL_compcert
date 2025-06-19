type effect = 
  | Divergence 
  | Read of string 
  | Write of string 
  | Alloc of string 
  | Io

type ptype = 
  | Tbool
  | Tuint8
  | Tint8
  | Tuint16
  | Tint16
  | Tuint32
  | Tint32
  | Tulong
  | Tlong

type typ = 
  | Utype
  | Vtype of ptype 

type const = 
  | Cunit 
  | Cbool of bool
  | Cint32 of int32
  | Clong of int64

(** The type of the abstract syntax tree (AST). *)
type expr =
  | Var of string
  | Const of const
  | Let of string * typ * expr * expr
  | If of expr * expr * expr

type fundecl =
  | Tfundecl of string * typ * effect list * (string * typ) list * (string * typ) list * expr

type toplevel =
  | Internal of fundecl
  | EBPFInternal of fundecl

type program = toplevel list

let rec collect_vars (e : expr) : (string * typ) list =
  match e with
  | Var _ -> []
  | Const _ -> []
  | Let (id, ty, e1, e2) ->
      (* Collect variables from both subexpressions and prepend current binding *)
      (id, ty) :: (collect_vars e1 @ collect_vars e2)
  | If (e1, e2, e3) ->
      collect_vars e1 @ collect_vars e2 @ collect_vars e3

