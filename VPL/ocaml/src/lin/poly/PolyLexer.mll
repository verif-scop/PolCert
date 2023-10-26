rule token
= parse
   | [' ' '\t'] {token lexbuf}
   | '-'?['0'-'9']+ as n {PolyParser.INT n}
   | ('-'?['0'-'9']+'/'['0'-'9']+['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*)
   | ('-'?['0'-'9']+['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*)
   | ('-'?['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*)
   | (['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*) as s {PolyParser.QxVar s} 
   | '+' {PolyParser.PLUS}
   | '*' | '.' {PolyParser.TIMES}
   | '/' {PolyParser.SLASH}
   | eof {PolyParser.EOF}
   | '-' {PolyParser.LESS}
   | '^' {PolyParser.EXP}
   |"<=" {PolyParser.LE}
   |"<" {PolyParser.LT}
   |">=" {PolyParser.GE}
   |">" {PolyParser.GT}
   |"=" {PolyParser.EQ}
   |"<>" {PolyParser.NEQ}
   |"," | '\n' {PolyParser.VRG}
   |";" {PolyParser.PVRG}
   |"(" {PolyParser.PARBEG}
   |")" {PolyParser.PAREND}
   |":=" {PolyParser.ASSIGN}
   | _ as c {Stdlib.failwith ("PolyLexer: " ^ String.make 1 c)}
and
token2 = parse
   | [' ' '\t'] {token2 lexbuf}
   | '-'?['0'-'9']+ as n {PolyParser.INT n}
   | ['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* as s {PolyParser.VAR s}
   | '+' {PolyParser.PLUS}
   | '*' {PolyParser.TIMES}
   | '/' {PolyParser.SLASH}
   | eof {PolyParser.EOF}
   | _ as c {Stdlib.failwith ("PolyLexer: " ^ String.make 1 c)}
