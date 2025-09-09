
(* The type of tokens. *)

type token = 
  | WRITE
  | UNIT
  | ULONGTYPE
  | UINT8TYPE
  | UINT32TYPE
  | UINT16TYPE
  | TILDE
  | THEN
  | STRUCT
  | STRING of (string)
  | STAR
  | SECTION of (string)
  | RULONGTYPE
  | RUINT8TYPE
  | RUINT32TYPE
  | RUINT16TYPE
  | RSTRUCT
  | RPAREN
  | RLONGTYPE
  | RINT8TYPE
  | RINT32TYPE
  | RINT16TYPE
  | READ
  | RBRACE
  | RBOOLTYPE
  | RAULONG
  | RAUINT8
  | RAUINT32
  | RAUINT16
  | RARRAY
  | RALONG
  | RAINT8
  | RAINT32
  | RAINT16
  | RABOOL
  | PLUS
  | NEG
  | LPAREN
  | LONGTYPE
  | LET
  | LBRACE
  | IO
  | INT8TYPE
  | INT64 of (int64)
  | INT32TYPE
  | INT32 of (int32)
  | INT16TYPE
  | IN
  | IF
  | IDENT of (string)
  | HASHEBPF
  | FUNTYPE
  | FUNC
  | EQ
  | EOF
  | EMPTYBRACKETS
  | ELSE
  | DIVERGENCE
  | COMMA
  | COLON
  | BOOLTYPE
  | BOOL of (bool)
  | ALLOC

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Beepl_ast.program)
