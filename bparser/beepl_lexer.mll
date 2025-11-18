(* beepl_lexer.mll *)
{
open Beepl_parser
open Lexing

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = lexbuf.lex_curr_pos; pos_lnum = pos.pos_lnum + 1 }
}

let whitespace = [' ' '	' '\r']
let newline = '\n'
let letter = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = letter (letter | digit)*
let identchar = letter | digit | '_'

rule read_token = parse
  | whitespace+     { read_token lexbuf }
  | newline         { next_line lexbuf; read_token lexbuf }
  | "fun"           { FUNC }
  | "let"           { LET }
  | "in"            { IN }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "for"           { FOR }
  | "Up"            { UP }
  | "Down"          { DOWN }
  | "struct"        { STRUCT }
  | "match"         { MATCH }
  | "with"          { WITH }
  | "->"            { ARROW }
  | "some"          { OSOME }
  | "none"          { ONONE }
  | "|"             { BAR }
  | "bytes"          { BYTES }
  | "Pbytes"         { PBYTES }
  | "ref"           { REF }
  | "!"             { DEREF }
  | ":="            { MASSGN }
  | "true"          { BOOL true }
  | "false"         { BOOL false }
  | "unit"          { UNIT }
  | "int8"          { INT8TYPE }
  | "uint8"         { UINT8TYPE }
  | "int16"         { INT16TYPE }
  | "uint16"        { UINT16TYPE }
  | "int32"         { INT32TYPE }
  | "uint32"        { UINT32TYPE }
  | "bool"          { BOOLTYPE }
  | "ulong"         { ULONGTYPE }
  | "long"          { LONGTYPE }
  | "bool*"         { RBOOLTYPE }
  | "int8*"         { RINT8TYPE }
  | "uint8*"        { RUINT8TYPE }
  | "int16*"        { RINT16TYPE }
  | "uint16*"       { RUINT16TYPE }
  | "int32*"        { RINT32TYPE }
  | "uint32*"       { RUINT32TYPE }
  | "long*"         { RLONGTYPE }
  | "ulong*"        { RULONGTYPE }
  | "struct*"       { RSTRUCT }
  | "oint8*"        { ORINT8TYPE }
  | "ouint8*"       { ORUINT8TYPE }
  | "oint16*"       { ORINT16TYPE }
  | "ouint16*"      { ORUINT16TYPE }
  | "oint32*"       { ORINT32TYPE }
  | "ouint32*"      { ORUINT32TYPE }
  | "olong*"        { ORLONGTYPE }
  | "oulong*"       { ORULONGTYPE }
  | "ostruct"      { ORSTRUCT }
  | "io"            { IO }
  | "divergence"    { DIVERGENCE }
  | "read"          { READ }
  | "write"         { WRITE }
  | "alloc"         { ALLOC }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | ":"             { COLON }
  | ","             { COMMA }
  | "="             { EQ }
  | "{"             { LBRACE }
  | "}"             { RBRACE }
  | "[" "]"         { EMPTYBRACKETS }
  | "struct"        { STRUCT }
  | '~'             { TILDE } (* Single token for overloaded use for notint and notbool *)
  | "+"             { PLUS }
  | "-"             { MINUS }
  | "*"             { MUL }
  | "/"             { DIV }
  | "%"             { MOD }
  | "&"             { AND }
  | "|"             { OR } 
  | "^"             { XOR }
  | "<<"            { SHL }
  | ">>"            { SHR }
  | "=="            { OEQ }
  | "!="            { NEQ }
  | "<"             { LT }
  | ">"             { GT }  
  | "<="            { LE }
  | ">="            { GE }
  | "."             { DOT }
  | "["             { LBRACK }
  | "]"             { RBRACK }
  | "array"         { ARRAY }
  | '"' ([^ '"' '\n']* as s) '"' { STRING s }

  
(* INT64 literals with L/l suffix *)
| digit+ ['l' 'L'] as l64 {
    let n = String.sub l64 0 (String.length l64 - 1) in
    try INT64 (Int64.of_string n) with
    | Failure _ -> raise (SyntaxError ("int64 literal out of range: " ^ n))
  }

(* plain digits: try int32, else fall back to int64 *)
| digit+ as n {
    try INT32 (Int32.of_string n) with
    | Failure _ ->
        try INT64 (Int64.of_string n) with
        | Failure _ -> raise (SyntaxError ("integer literal out of range: " ^ n))
  }

  | ident as id     { IDENT id }
  | "#ebpf"         { HASHEBPF }
  (* #section "<anything but newline and unescaped quote>" *)
  | "#section" whitespace+ (letter identchar*) as id { SECTION id }

  (* #section path/like/name allowing / . - _ after the first char *)
  | "#section" whitespace+ (letter (letter | digit | '_' | '/' | '.' | '-')*) as id { SECTION id }
  | eof             { EOF }
  | _               { raise (SyntaxError ("Unrecognized character: " ^ Lexing.lexeme lexbuf)) }
  | "(*"          { comment lexbuf }


and comment = parse
  | "*)"        { read_token lexbuf }  (* End of comment *)
  | "(*"        { ignore (comment lexbuf); comment lexbuf }  (* Nested comment *)
  | '\n'        { next_line lexbuf; comment lexbuf }
  | eof         { raise (SyntaxError "Unterminated comment") }
  | _           { comment lexbuf }