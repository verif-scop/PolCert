rule token
= parse
   | [' ' '\t'] {token lexbuf}
   | '\n' {PLPParser.EOL}
   | "simplex" {PLPParser.SX}
   | "matrix" {PLPParser.MATRIX}
 	| "boundaries" {PLPParser.FRONTIERS}
 	| "no boundaries" {PLPParser.NO_FRONTIERS}
 	| "exp" {PLPParser.EXPLORATION_POINT}
 	| "todo" {PLPParser.TODO}
 	| "region" {PLPParser.REGION}
 	| "problem" {PLPParser.PROBLEM}
 	| "no point" {PLPParser.NO_POINT}
 	| "points" {PLPParser.POINTS}
   | '/' {PLPParser.SLASH}
   | '-'?['0'-'9']+ as n {PLPParser.Z (Z.of_string n)}
   | eof {PLPParser.EOF}
