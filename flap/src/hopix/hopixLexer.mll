{ (* -*- tuareg -*- *)
  open Lexing
  open Error
  open Position
  open HopixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

(* Nombre en base 10 et en base 16 *)
let digit = ['0'-'9']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F'] 
let bindigit = ['0'-'1']
let octdigit = ['0'-'7']

(* var_id, label_id et type_con 
on fera la diff dans le parser *)
let ident = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

(* constr_id *)
let id_data_const =['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* 

(* type_variable *)
let type_variable = '`'ident

(* int *)
let int = '-'? digit+ 
  |"0x"hexdigit+ 
  |"0b"bindigit+
  |"0o"octdigit+

let printable = ['\033'- '\038'  '\040' - '\126']

let escape = 
  "\\\\" 
  | "\\'" 
  | "\\n" 
  | "\\t" 
  | "\\b" 
  | "\\r"

let atom = 
  ['\000'-'\255'] 
  | "\\0x" hexdigit hexdigit
  | printable 
  | escape


let printable_s =['\035'- '\038'  '\040' - '\126'] | '\033' 


(* le atom dans les guillemets doubles pour le string *)
let atom_s = 
  ['\000'-'\255'] 
  | "\\0x" hexdigit hexdigit
  | printable_s
  | escape


let char = '\'' atom '\'' 

(* string qui utilise atom_s *)
let string = '"' ((atom_s | ''' |'\"') ) * '"'


let single_line_comment = "##" [^ '\010' '\013']* newline


rule token = parse
  (* Comments ignore *)
  | single_line_comment { token lexbuf }
  | "{*" { comment lexbuf }
  

  (* Keywords *)
  | "let" {LET}
  | "fun" {FUN}
  | "and" {AND}
  | "if" {IF}
  | "match" {MATCH}
  | "then" {THEN}
  | "else" {ELSE}
  | "while" {WHILE}
  | "do" {DO}
  | "until" {UNTIL}
  | "for" {FOR}
  | "from" {FROM}
  | "to" {TO}
  | "type" {TYPE}
  | "extern" {EXTERN}
  | "ref" {REF}

  (* Symbols *)
  | "<"  {LANGLE}
  | ">" {RANGLE}
  | "," {COMMA}
  | "." {DOT}
  | ":" {COLON}
  | ";" {SEMICOLON}
  | "!" {EXCLAMATION}
  | "\\" {ANTISLASH}
  | "|" {PIPE}
  | "&" {CONJONCTION}
  | "->" {ARROW}
  | "("  {LPAREN}
  | ")" {RPAREN}
  | "{" {RCURLYB}
  | "}" {LCURLYB}
  | "[" {RSQUAREB}
  | "]" {LSQUAREB}
  | "_" {UNDERSCORE}
  

  (* Operation *)
  | ":=" {AFFECTATION}
  | "+" {PLUS}
  | "-" {MINUS}
  | "*" {TIMES}
  | "/" {DIV}
  | "=" {EQUAL}
  | "&&" {LOGAND}
  | "||" {LOGOR}
  | "=?" {EQUALITY}
  | "<=?" {LESS_OR_EQ}
  | ">=?" {GREATER_OR_EQ}
  | "<?" {LESS}
  | ">?" {GREATER}
  

  (* Regexs *)
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | ident {ID (Lexing.lexeme lexbuf)}
  | id_data_const {DATAID (Lexing.lexeme lexbuf)}
  | type_variable {TVAR (Lexing.lexeme lexbuf)}
  | char { CHAR (Lexing.lexeme lexbuf)}
  | string {STR (Lexing.lexeme lexbuf)}
  

  (* Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }
  | eof             { EOF       }

  (* Lexing error. *)
  | _               { error lexbuf "unexpected character." }



and comment = parse
  | "*}"           { token lexbuf }
  | "{*"           { let a = comment lexbuf in comment lexbuf; }
  | newline        { next_line_and comment lexbuf }
  | _              { comment lexbuf }

