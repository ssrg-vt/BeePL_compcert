type ident = string


type typ =
  | TName  of string
  | TRef   of typ
  | TArrow of typ list * typ


type pattern =
  | PWildcard
  | PUnit
  | PIdent  of ident
  | PAnnot  of pattern * typ


type param = ident * typ option


type expr =
  | EUnit
  | EInt32  of string
  | EVar    of ident
  | EApply  of expr * expr list
  | ELet    of pattern * typ option * expr * expr

  | ERef    of expr
  | EDeref  of expr
  | EAssign of expr * expr
  | EBlock  of expr list


type toplevel =
  | TLLet  of pattern * typ option * expr
  | TLFunc of ident * param list * typ option * expr
  | TLExpr of expr

type program = toplevel list
