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
    (* Char de la forme '\000'*)
    | _ when String.length s = 4 && s.[0] == '\\' ->
        Char.chr (int_of_string (String.sub s 1 3))
    | _ -> failwith "Invalid escape sequence"

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

let escape_3digits = 
  "\\" ['0'-'1'] ['0'-'9'] ['0'-'9']
  | "\\" "2" ['0'-'5'] ['0'-'5']

let atom = 
  escape_3digits
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


let char = "\'" atom "\'"

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
  | "{" {LCURLYB}
  | "}" {RCURLYB}
  | "[" {LSQUAREB}
  | "]" {RSQUAREB}
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
  (* Reconnait une chaîne string et renvoie une erreur si la string est mal formée *)
  | '"' { read_string (Buffer.create 16) lexbuf }
  
 
  (* Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }
  | eof             { EOF       }

  (* Lexing error. *)
  | _ as c            { error lexbuf ("Error (lexing)\nunexpected character.") }

and read_string buf = parse
  (* Fin de la string *)
  | '"'       { STR (Buffer.contents buf) }
  (* Cas d'erreur : string non fermée *)
  | eof       { error lexbuf "Unterminated string." }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' '"'  { Buffer.add_char buf '"'; read_string buf lexbuf }
  | '\\' '\'' { Buffer.add_char buf '\''; read_string buf lexbuf }
  | '\\' '0' 'x' (hexdigit hexdigit as hex)
      { Buffer.add_char buf (Char.chr (int_of_string ("0x" ^ hex)));
        read_string buf lexbuf }
  | '\\' (['0'-'1'] ['0'-'9'] ['0'-'9'] as digits)
      { Buffer.add_char buf (Char.chr (int_of_string digits));
        read_string buf lexbuf }
  | '\\' '2' (['0'-'5'] ['0'-'5'] as digits)
      { Buffer.add_char buf (Char.chr (int_of_string ("2" ^ digits)));
        read_string buf lexbuf }
  | newline   { next_line_and (read_string buf) lexbuf }
  | _ as c    { Buffer.add_char buf c; read_string buf lexbuf }

and comment = parse
  | "*}"           { token lexbuf }
  | "{*"           { let a = comment lexbuf in comment lexbuf; }
  | newline        { next_line_and comment lexbuf }
  | _              { comment lexbuf }

