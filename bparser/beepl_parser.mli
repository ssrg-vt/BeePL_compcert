
(* The type of tokens. *)

type token = 
  | XOR
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
  | SHR
  | SHL
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
  | OR
  | OEQ
  | NEQ
  | NEG
  | MUL
  | MOD
  | MINUS
  | LT
  | LPAREN
  | LONGTYPE
  | LET
  | LE
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
  | GT
  | GE
  | FUNTYPE
  | FUNC
  | EQ
  | EOF
  | EMPTYBRACKETS
  | ELSE
  | DIVERGENCE
  | DIV
  | COMMA
  | COLON
  | BOOLTYPE
  | BOOL of (bool)
  | AND
  | ALLOC

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Beepl_ast.program)
