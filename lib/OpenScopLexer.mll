{
open Lexing
open OpenScopParser
open Printf
open Camlcoq

exception LexError of string

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let currentLoc (lb: lexbuf) =
  let p = Lexing.lexeme_start_p lb in
  OpenScopAST.({ lineno   = p.Lexing.pos_lnum;
              filename = p.Lexing.pos_fname;
              byteno   = p.Lexing.pos_cnum;})

let keywords : (string, OpenScopAST.location -> token) Hashtbl.t = Hashtbl.create 6
let _ =
  List.iter (fun (key, builder) -> Hashtbl.add keywords key builder)
    [ 
      ("CONTEXT", fun loc -> CONTEXT loc);
      ("DOMAIN", fun loc -> DOMAIN loc);
      ("READ", fun loc -> READ loc);
      ("WRITE", fun loc -> WRITE loc);
      ("MAYWRITE", fun loc -> MAYWRITE loc);
      ("SCATTERING", fun loc -> SCATTERING loc);
    ]

let tags : (string, OpenScopAST.location -> token) Hashtbl.t = Hashtbl.create 30
let _ =
  List.iter (fun (key, builder) -> Hashtbl.add tags key builder)
    [ ("<OpenScop>", fun loc -> OPENSCOP loc);
      ("</OpenScop>", fun loc -> OPENSCOPEND loc);
      ("<strings>", fun loc -> STRINGS loc);
      ("</strings>", fun loc -> STRINGSEND loc);
      ("<body>", fun loc -> BODY loc);
      ("</body>", fun loc -> BODYEND loc);
      ("<arrays>", fun loc -> ARRAYS loc);
      ("</arrays>", fun loc -> ARRAYSEND loc);
      ("<coordinates>", fun loc -> COORD loc);
      ("</coordinates>", fun loc -> COORDEND loc);
      ("<scatnames>", fun loc -> SCATNAMES loc);
      ("</scatnames>", fun loc -> SCATNAMESEND loc);
      ("<loop>", fun loc -> LOOP loc);
      ("</loop>", fun loc -> LOOPEND loc);
    ]
}

let digit = ['0'-'9']
let nondigit = ['_' 'a'-'z' 'A'-'Z']
let nonbreak = [^ '\n']

let ident = ('$'|nondigit) (nondigit|digit)*
let line = nonbreak* 
(* Whitespaces *)
let whitespace = [' ' '\t'  '\011' '\012' '\r']+

(* Integer constants *)
(* let sign = ['-'] as signpart *)
let decimal_constant = (digit+ as intpart)

let sign = ['-' '+']
let digit_sequence = digit+
let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
let decimal_floating_constant = fractional_constant 

let newline = '\n'
let ident = ['a'-'z' 'A'-'Z' '_' '$'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let tag = ['<'] ident ['>'] | ['<'] '/' ident ['>']
(* part "4" *)
rule read =
  parse
  | whitespace    { read lexbuf }
  | newline  { let loc = (currentLoc lexbuf) in new_line lexbuf; NEWLINE loc }
  | '#'      { singleline_comment lexbuf }
  | '['      { LBRACK }
  | ']'      { RBRACK }
  | '('      { LPAREN }
  | ')'      { RPAREN }
  | "+="     { ADDASSIGN }
  | "-="     { SUBASSIGN }
  | "/="     { DIVASSIGN }
  | "*="     { MULTIASSIGN }
  | "<"      { LT }
  | "<="     { LE }
  | "?"      { QUESTION }
  | ":"      { COLON }
  | ","      { COMMA }
  | '='      { EQUAL }
  | '+'      { PLUS }
  | '-'      { MINUS }
  | '*'      { MULTI }
  | '/'      { DIV }
  | ';'      { SEMI }
  | "(null)" {NULLFILE}
  | tag as tag
    { 
      try
        Hashtbl.find tags tag (currentLoc lexbuf)
      with Not_found ->
        raise (LexError ("Invalid tag: " ^ tag))
    }
  | ident as id
    { try
        Hashtbl.find keywords id (currentLoc lexbuf)
      with Not_found ->
        IDENT (id, (currentLoc lexbuf)) 
        (* raise (LexError ("Invalid keyword: " ^ id)) *)
    }
  | decimal_constant as c
      { 
        INT (c, (currentLoc lexbuf))
      }
  | decimal_floating_constant as c 
      {
        FLOAT (intpart, frac, (currentLoc lexbuf))
      }
  | eof  { EOF }
  | _ { raise (LexError ("Invalid symbol: " ^ lexeme lexbuf)) }
(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | newline   { 
      let loc = (currentLoc lexbuf) in new_line lexbuf; NEWLINE loc 
    }
  | eof    { EOF }
  | _      { singleline_comment lexbuf }

