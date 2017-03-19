	%{
           open ScTypes 
        %}
	%token EOF
	%token <string> INT
        %token PLUS MINUS TIMES DIV MOD
        %token LPRN RPRN LCBR RCBR
        %token OR AND IMP NOT
        %token SEMI CLN FUN
        %token RANGE
        %token LESS GRTR EQLS NEQL LEQL GEQL
        %token DOT NULL COMMA
        %token <string> STR
        %left IMP
        %left OR
        %left AND
        %left EQLS NEQL 
        %left LESS GRTR LEQL GEQL
        %left PLUS MINUS       
        %left TIMES DIV MOD 
        %left UMINUS
        %right NOT
        %left LCBR DOT
        %left RPRN LPRN
        %start main
        %type <ScTypes.expr> expr
        %type <string list> sseq1
        %type <string list> sseq
        %type <int * int * string * ScTypes.expr * string list> main 
        %%
        main: 
            INT INT STR expr SEMI sseq1 EOF { ((int_of_string($1)),(int_of_string($2)),$3,$4,$6) } 
        ;
        c_name:
          | STR			{ $1 }
          | STR DOT c_name      { $1^"."^$3 }
        ;
        sseq1:
          |          { [] } 
	  | sseq     { $1 };
        sseq:
          | c_name      	          { [$1]   }
          | c_name COMMA sseq		  { $1::$3 }
        ;
        expr:
             | expr PLUS expr     { BinOp($1,"+",$3) }
             | expr MINUS expr    { BinOp($1,"-",$3) }
             | expr TIMES expr    { BinOp($1,"*",$3) }
             | expr DIV expr      { BinOp($1,"/",$3) }
             | expr MOD expr      { BinOp($1,"%",$3) }
             | expr LESS expr     { BinOp($1,"<",$3) }
             | expr GRTR expr     { BinOp($1,">",$3) }
             | expr LEQL expr     { BinOp($1,"<=",$3) }
             | expr GEQL expr     { BinOp($1,">=",$3) }
             | expr EQLS expr     { BinOp($1,"==",$3) }
             | expr NEQL expr     { BinOp($1,"!=",$3) }
             | expr OR expr       { BinOp($1,"||",$3) }
             | expr AND expr      { BinOp($1,"&&",$3) }
             | expr IMP expr      { Imp($1,"->",$3)   }
             | NOT expr           { Not($2)           }
             | LPRN expr RPRN     { $2 }
             | expr DOT STR LPRN STR CLN c_name FUN expr RPRN   
            { if $3="forall" then Forall($1,Str($5),Str($7),$9) else
              if $3="exists" then Exists($1,Str($5),Str($7),$9) else
              if $3="filter" then Filter($1,Str($5),Str($7),$9) else
              if $3="map" then Map($1,Str($5),Str($7),$9) else
              raise Parsing.Parse_error} 
             | RANGE LPRN expr COMMA expr RPRN DOT STR LPRN STR CLN STR FUN expr RPRN 
            { if ($8<>"forall"&&$8<>"exists"&&$8<>"filter"&&$8<>"map") then raise Parsing.Parse_error else
              Range($3,$5,$8,Str($10),Str($12),$14) }
             | INT                                 { Int($1)           }
             | MINUS INT  %prec UMINUS             { Int("-"^$2)       }
             | STR                                 { Str($1)           }
             | NULL                                { Null("null")      }
             | expr DOT STR                        { Field($1,Str($3)) } 
             | expr LCBR expr RCBR                 { Arr_elm($1,$3)    }
             | expr DOT STR LPRN prmlst RPRN       { Method($1,Str($3),$5) }
             | STR LPRN prmlst RPRN                { StaticM(Str($1),$3) }
             | STR LPRN expr COMMA STR CLN STR FUN STR LPRN prmlst RPRN RPRN 
            { if ($9<>"List"&&$1<>"reachable") then raise Parsing.Parse_error else Reach($3,Str($5),Str($7),$11) }
        ;
        prmlst:
          |                  { [] }
          | prm_aux          { $1 }
          
	;
        prm_aux:
          | expr COMMA prm_aux      { $1::$3  }
          | expr                    { [$1] }
        ;
