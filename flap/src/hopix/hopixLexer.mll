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

let digit = ['0'-'9']

let ident = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let id_data_const =['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* 

let type_variable = '`'ident

let int = '-'? digit | "0x"['0'-'9' 'a'-'f' 'A'-'F']+ | "0b"['0'-'1'] +

let atom = ['\000'-'\255'] | "\\0x" ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
     | [' '-'~']# ''' | "\\" | "\'" | '\n' | '\t' | '\b'| '\r'



let char = '\'' atom '\'' 
let string = '"' (atom # ['"'] | '\'')* '"'




rule token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }
  | eof             { EOF       }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }

