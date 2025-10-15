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


  let interpret_char s =
    match s with
    | "\\n" -> '\n'
    | "\\t" -> '\t'
    | "\\b" -> '\b'
    | "\\r" -> '\r'
    | "\\\\" -> '\\'
    | "\\'" -> '\''
    | _ when String.length s > 3 && s.[0] = '\\' && s.[1] = '0' && s.[2] = 'x' ->
        let hex = String.sub s 3 2 in
        Char.chr (int_of_string ("0x" ^ hex))
    | _ when String.length s = 1 -> s.[0]
    | _ -> failwith "Invalid escape sequence"

  (* Fonction pour interpréter une string *)
  let interpret_string s =
    let buf = Buffer.create (String.length s) in
    let rec loop i =
      if i >= String.length s then Buffer.contents buf
      else if s.[i] = '\\' && i + 1 < String.length s then
        match s.[i+1] with
        | 'n' -> Buffer.add_char buf '\n'; loop (i+2)
        | 't' -> Buffer.add_char buf '\t'; loop (i+2)
        | 'b' -> Buffer.add_char buf '\b'; loop (i+2)
        | 'r' -> Buffer.add_char buf '\r'; loop (i+2)
        | '\\' -> Buffer.add_char buf '\\'; loop (i+2)
        | '"' -> Buffer.add_char buf '"'; loop (i+2)
        | '\'' -> Buffer.add_char buf '\''; loop (i+2)
        | '0' when i + 4 < String.length s && s.[i+2] = 'x' ->
            let hex = String.sub s (i+3) 2 in
            Buffer.add_char buf (Char.chr (int_of_string ("0x" ^ hex)));
            loop (i+5)
        | _ -> Buffer.add_char buf s.[i]; loop (i+1)
      else (Buffer.add_char buf s.[i]; loop (i+1))
    in loop 0
  

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
  | int { try INT (Mint.of_string (Lexing.lexeme lexbuf)) with | _ -> error lexbuf "Integer literal too large."}
  | ident {ID (Lexing.lexeme lexbuf)}
  | id_data_const {DATAID (Lexing.lexeme lexbuf)}
  | type_variable {TVAR (Lexing.lexeme lexbuf)}
  | char { 
      let s = Lexing.lexeme lexbuf in
      (* Enlève guillemets *)
      let content = String.sub s 1 (String.length s - 2) in
      CHAR (interpret_char content)
    }
  | string {
      let s = Lexing.lexeme lexbuf in
      (* Enlève les guillemets *)
      let content = String.sub s 1 (String.length s - 2) in
      STR (interpret_string content)
  }
  
 
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

