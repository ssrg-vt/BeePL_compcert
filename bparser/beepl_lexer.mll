{
open Beepl_parser
open Lexing

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = lexbuf.lex_curr_pos; pos_lnum = pos.pos_lnum + 1 }
}

let whitespace = [' ' '\t' '\r']
let newline = '\n'
let letter = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = letter (letter | digit)*

rule read_token = parse
  | whitespace+     { read_token lexbuf }
  | newline         { next_line lexbuf; read_token lexbuf }
  | "fun"           { FUNC }
  | "let"           { LET }
  | "in"            { IN }
  | "if"            { IF }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "true"          { BOOL true }
  | "false"         { BOOL false }
  | "unit"          { UNIT }
  | "int"           { INT32TYPE }
  | "bool"          { BOOLTYPE }
  | "long"          { LONGTYPE }
  | "io"            { IO }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | ":"             { COLON }
  | ","             { COMMA }
  | "="             { EQ }
  | "{"             { LBRACE }
  | "}"             { RBRACE }

  | '-'? digit+ as i32 { INT32 (Int32.of_string i32) }
  | '-'? digit+ ['l' 'L'] as l64 {
      let n = String.sub l64 0 (String.length l64 - 1) in
      INT64 (Int64.of_string n)
    }

  | ident as id     { IDENT id }
  | eof             { EOF }
  | _               { raise (SyntaxError ("Unrecognized character: " ^ Lexing.lexeme lexbuf)) }
