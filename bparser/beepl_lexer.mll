{
open Beepl_parser
open Lexing

exception SyntaxError of string


let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}


let digit = ['0'-'9']
let int = digit+
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '.']*

rule read =
  parse
  | white    { read lexbuf }
  | newline  { next_line lexbuf; read lexbuf }
  | "let"    { LET }
  | "func"   { FUNC }
  | "in"     { IN }
  | "ref"    { REF }
  | "()"     { UNIT }
  | "("      { LPAREN }
  | ")"      { RPAREN }
  | "="      { EQUAL }
  | ":"      { COLON }
  | "->"     { ARROW }
  | "!"      { BANG }
  | ":="     { ASSIGN }
  | "_"      { UNDERSCORE }
  | int as num         { INT32 num }
  | id       { IDENT (Lexing.lexeme lexbuf) }
  | "(*"     { comment 0 lexbuf }
  | _        { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }

and comment level =
  parse
  | "*)"     { if level = 0 then read lexbuf else comment (level - 1) lexbuf }
  | "(*"     { comment (level + 1) lexbuf }
  | newline  { next_line lexbuf; comment level lexbuf }
  | _        { comment level lexbuf }
  | eof      { raise (SyntaxError "Unclosed comment") }
