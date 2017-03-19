	{
        open ScParser
        }
        let ident = ['$' '_' 'a'-'z' 'A'-'Z'](['$' '_' 'a'-'z' 'A'-'Z' '0'-'9']*)
        rule token = parse
            [' ' '\t' '\n']     { token lexbuf }
          | '+'                 { PLUS }
          | '-'                 { MINUS }
          | '*'                 { TIMES }
          | '/'                 { DIV }
          | '%'                 { MOD }
          | "("                 { LPRN }
          | ")"                 { RPRN }
          | "["		        { LCBR }
          | "]"                 { RCBR }
          | "||" 	        { OR }
  	  | "&&"	        { AND }
	  | "->" 	        { IMP }
  	  | '!' 	        { NOT }
          | ';'                 { SEMI }
	  | ':' 	        { CLN }
  	  | "=>" 	        { FUN }
  	  | '<'  	        { LESS }
  	  | '>'  	        { GRTR }
  	  | "==" 	        { EQLS }
  	  | "!=" 	        { NEQL }
  	  | "<=" 	        { LEQL }
  	  | ">=" 	        { GEQL }
          | "."                 { DOT }
          | ","                 { COMMA }
          | "range"             { RANGE }
          | "null"              { NULL }
          | ['0'-'9']+ as lxm   { INT(lxm); }
          | ident as lxm        { STR(lxm) }
          | eof                 { EOF }
