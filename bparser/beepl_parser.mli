
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
  | REF
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
  | OSTRUCT
  | ORULONGTYPE
  | ORUINT8TYPE
  | ORUINT32TYPE
  | ORUINT16TYPE
  | ORSTRUCT
  | ORLONGTYPE
  | ORINT8TYPE
  | ORINT32TYPE
  | ORINT16TYPE
  | ORBOOLTYPE
  | ORAULONG
  | ORAUINT8
  | ORAUINT32
  | ORAUINT16
  | ORARRAY
  | ORALONG
  | ORAINT8
  | ORAINT32
  | ORAINT16
  | ORABOOL
  | OR
  | OEQ
  | NEQ
  | NEG
  | MUL
  | MOD
  | MINUS
  | MASSGN
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
  | DEREF
  | COMMA
  | COLON
  | CAST
  | BOOLTYPE
  | BOOL of (bool)
  | AND
  | ALLOC

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Beepl_ast.program)
