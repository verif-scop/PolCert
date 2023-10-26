[@@@part "0"] ;;
open Lexing
open Printf
open Exceptions 


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Some (OpenScopParser.openscop OpenScopLexer.read lexbuf) with
  | OpenScopLexer.LexError msg ->
    printf "%a: %s\n" print_position lexbuf msg;
    None
  | OpenScopParser.Error ->
    printf "%a: syntax error\n" print_position lexbuf;
    None

let parse_and_print filename outfilename lexbuf =
  match parse_with_error lexbuf with
  | Some p ->
     (try
        let p = (OpenScopAST2OpenScop.convert p) in 
        OpenScopPrinter.openscop_printer outfilename p;
        Some p
      with
      | CompilationError -> None)
  | None -> None;;

let read_and_print filename outfilename = 
  let inx = open_in filename in 
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let oscop = parse_and_print filename outfilename lexbuf in 
  close_in inx; oscop ;;

let read filename = 
  let inx = open_in filename in 
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  match parse_with_error lexbuf with
  | Some p ->
     (try
        let p = (OpenScopAST2OpenScop.convert p) in 
        close_in inx; Some p
      with
      | CompilationError -> close_in inx; None)
  | None -> None
  ;;
