
open ScTypes

let all_suffix = ref 0
let xst_suffix = ref 0
let discrepancy = ref 0
let level = ref 0

exception Fail of string

let static = ref ""

let create_file = output_string (open_out (Sys.argv.(1)^"_out")) ("")

let write = output_string  (open_out_gen [Open_append] 0o666 (Sys.argv.(1)^"_out"))

(* consider return type void *)


let rec union l = match l with 
	    | [] -> []
	    | x :: xs -> [x] @ (union (List.filter (fun y->y<>x) xs));;

let rec add_last lst elm = match lst with
                   | [] -> elm::[]
                   | head::tail -> head::(add_last tail elm)

let rec contains var set = match set with
                   | [] -> false
                   | (x,y)::tail -> if (x=var) then true else (contains var tail)

let rec second var set = match set with
                   | [] -> raise (Fail "not found")
                   | (x,y)::tail -> if (x=var) then (x,y) else (second var tail)

let index = ref 0 
                   
let rec print_list = function
                   | [] -> index:=0; ""
                   | head::[] -> incr index; head^" $"^(string_of_int(!index))^(print_list [])
                   | head::tail -> incr index; head^" $"^(string_of_int(!index))^", "^(print_list tail)

let rec print_parameters = function
                   | (x,y)::[] -> (y^" "^(if((String.sub x 0 1)="$") then "_"^x else x)^")")
                   | (x,y)::tail -> (y^" "^(if((String.sub x 0 1)="$") then "_"^x else x)^", ")^print_parameters tail
                   | [] -> (")")

let rec print_vars = function 
 	           | (x,y)::[] -> x^")"
                   | (x,y)::tail -> (x^", ")^print_vars tail
                   | [] -> ")"

let reach_body root var_name t_var = "java.util.Set set = new java.util.HashSet();\n" ^ "java.util.Stack stack = new" ^
"java.util.Stack(); \n"^ "stack.push("^root^");\nwhile(!stack.isEmpty()){\n"^ t_var^" "^var_name^" = ("^t_var^") " ^ 
"stack.pop();\n"

let print_all_rest = ("  if(!test){\n    return false; }\n  }\n"^"  return true;\n}\n*/\n")

let print_xst_rest = ("  if(test){\n    return true; }\n  }\n"^"  return false;\n}\n*/\n")



let rec expr_to_string env prmlst param = match param with
                 | Int x -> x
                 | Str x -> if((!discrepancy)=1&&((String.sub x 0 1)="$")) then "_"^x else x
                 | Null _ -> "null"
                 | Field (x,y) -> (expr_to_string env prmlst x)^"."^(expr_to_string env prmlst y)
                 | Arr_elm(ident,index) -> (expr_to_string env prmlst ident)^"["^(expr_to_string env prmlst index)^"]"
                 | Method(obj,m_name,p_lst) -> (expr_to_string env prmlst obj)^"."^(expr_to_string env prmlst m_name)^"("^
                          (print_meth_call_prm p_lst env prmlst)^")"
                 | StaticM(m_name,p_lst) -> (expr_to_string env prmlst m_name)^"("^
                          (print_meth_call_prm p_lst env prmlst)^")"
                 | Reach(first_elt,local,local_t,p_list) -> let root = (expr_to_string env prmlst first_elt) in
let var_name = (expr_to_string env prmlst local) in let t_var = (expr_to_string env prmlst local_t) in
                                write 
("/*\npublic "^(!static)^" HashSet forall"^(string_of_int(!all_suffix))^"("^root^"){\n"^(reach_body root var_name t_var)^ 
(print_rch_rest p_list env prmlst)^"}\nreturn set;\n}\n" );
		       incr all_suffix;	
			("forall"^(string_of_int((!all_suffix)-1))^"("^root^")")
                 | BinOp(expr1,operator,expr2) -> "("^(expr_to_string env prmlst expr1)^operator^(expr_to_string env prmlst expr2)^") "
                 | Imp(expr1,operator,expr2) -> "!("^(expr_to_string env prmlst expr1)^") || ("^(expr_to_string env prmlst expr2)^")"
                 | Not x -> "!"^(expr_to_string env prmlst x)
                 | Filter(set_name,var_name,t_var,stmt) -> discrepancy:=1; level:=(!level)+1; let all_with_duplicates = 
                                    (all_variables env prmlst set_name)@(all_variables env prmlst stmt) in 
                                       let all = union all_with_duplicates in 
                                write
("/*\npublic "^(!static)^" HashSet forall"^(string_of_int(!all_suffix))^"("^(print_parameters all)^(print_filter set_name t_var var_name env prmlst)^(expr_to_string ((expr_to_string env prmlst var_name,expr_to_string env prmlst t_var)::env) prmlst stmt)^");\n"^(print_flt_rest var_name));
                       incr all_suffix; level:=(!level)-1; if(!level=0)then discrepancy:=0;
			("forall"^(string_of_int((!all_suffix)-1))^"("^(print_vars all))
                 | Map(set_name,var_name,t_var,stmt) -> discrepancy:=1; level:=(!level)+1; let all_with_duplicates = 
                                    (all_variables env prmlst set_name)@(all_variables env prmlst stmt) in 
                                       let all = union all_with_duplicates in 
                                write
("/*\npublic "^(!static)^" HashSet forall"^(string_of_int(!all_suffix))^"("^(print_parameters all)^(print_map set_name t_var var_name env prmlst)^(expr_to_string ((expr_to_string env prmlst var_name,expr_to_string env prmlst t_var)::env) prmlst stmt)^");\n"^(print_map_rest var_name));
                       incr all_suffix; level:=(!level)-1; if(!level=0)then discrepancy:=0;
			("forall"^(string_of_int((!all_suffix)-1))^"("^(print_vars all))
                 | Forall(set_name,var_name,t_var,stmt) -> discrepancy:=1; level:=(!level)+1; let all_with_duplicates = 
                                    (all_variables env prmlst set_name)@(all_variables env prmlst stmt) in 
                                       let all = union all_with_duplicates in 
                                write 
("/*\npublic "^(!static)^" boolean forall"^(string_of_int(!all_suffix))^"("^(print_parameters all)^(print_body set_name t_var var_name env prmlst)^(expr_to_string ((expr_to_string env prmlst var_name,expr_to_string env prmlst t_var)::env) prmlst stmt)^");\n"^(print_all_rest));
                       incr all_suffix; level:=(!level)-1; if(!level=0)then discrepancy:=0;
			("forall"^(string_of_int((!all_suffix)-1))^"("^(print_vars all))
                 | Exists(set_name,var_name,t_var,stmt) -> discrepancy:=1; level:=(!level)+1; let all_with_duplicates = 
                                    (all_variables env prmlst set_name)@(all_variables env prmlst stmt) in 
                                       let all = union all_with_duplicates in 
                                write
("/*\npublic "^(!static)^" boolean exists"^(string_of_int(!xst_suffix))^"("^(print_parameters all)^(print_body set_name t_var var_name env prmlst)^(expr_to_string ((expr_to_string env prmlst var_name,expr_to_string env prmlst t_var)::env) prmlst stmt)^");\n"^(print_xst_rest));
                       incr xst_suffix; level:=(!level)-1; if(!level=0)then discrepancy:=0;
			("exists"^(string_of_int((!xst_suffix)-1))^"("^(print_vars all))
                 | Range(x,y,"forall",var_name,t_var,stmt) -> let set_name = ("new RangeSet("^(expr_to_string env prmlst x)^","^(expr_to_string env prmlst y)^")") in (expr_to_string env prmlst (Forall(Str(set_name),var_name,t_var,stmt)))
                 | Range(x,y,"exists",var_name,t_var,stmt) -> let set_name = ("new RangeSet("^(expr_to_string env prmlst x)^","^(expr_to_string env prmlst y)^")") in (expr_to_string env prmlst (Exists(Str(set_name),var_name,t_var,stmt)))
                 | Range(x,y,"filter",var_name,t_var,stmt) -> let set_name = ("new RangeSet("^(expr_to_string env prmlst x)^","^(expr_to_string env prmlst y)^")") in (expr_to_string env prmlst (Filter(Str(set_name),var_name,t_var,stmt)))
                 | Range(x,y,"map",var_name,t_var,stmt) -> let set_name = ("new RangeSet("^(expr_to_string env prmlst x)^","^(expr_to_string env prmlst y)^")") in (expr_to_string env prmlst (Map(Str(set_name),var_name,t_var,stmt)))
                 | Range(_,_,_,_,_,_) -> raise (Fail "impossible")

and all_variables env prmlst ast = match ast with
                   | Int _ -> []
                   | Str x -> if((x<>"$0")&&((String.sub x 0 1)="$")) then 
                          (if (x="$_") then [(x,(List.nth prmlst (List.length prmlst - 1)))] else
                            (let ind = int_of_string(String.sub x 1 ((String.length x)-1)) in
                                    (if (ind > (List.length prmlst)) then 
                                         raise (Fail "invalid parameter") else [(x,(List.nth prmlst (ind-1)))]))) else
                                              if (contains x env)then [(second x env)] else [] 
                   | Null _ -> []
                   | Field (x,_) -> (all_variables env prmlst x)
                   | Arr_elm(x,y) -> (all_variables env prmlst x)@(all_variables env prmlst y)
                   | Method(obj,_,p_list) -> (all_variables env prmlst obj)@(List.flatten (List.map (all_variables env 													prmlst) p_list))
                   | StaticM(_,p_list) -> (List.flatten (List.map (all_variables env prmlst) p_list))
                   | Filter(set_name,var_name,t_var,stmt) 
                   | Map(set_name,var_name,t_var,stmt) -> 
                         if ((String.sub (expr_to_string env prmlst var_name) 0 1) ="$") then
                             raise (Fail "the name of set elements can't start with $")  
                                 else (all_variables env prmlst set_name)@all_variables env prmlst stmt
                   | Reach(var,_,_,_)-> all_variables env prmlst var
                   | BinOp(expr1,operator,expr2)   
                   | Imp(expr1,operator,expr2) -> (all_variables env prmlst expr1)@(all_variables env prmlst expr2 )
                   | Not x -> all_variables env prmlst x
                   | Forall(set_name,var_name,t_var,stmt) 
                   | Exists(set_name,var_name,t_var,stmt) -> 
                         if ((String.sub (expr_to_string env prmlst var_name) 0 1) ="$") then
                             raise (Fail "the name of set elements can't start with $")  
                                 else (all_variables env prmlst set_name)@all_variables env prmlst stmt
                   | Range(_,_,_,var_name,t_var,stmt) -> 
                         if ((String.sub (expr_to_string env prmlst var_name) 0 1) ="$") then
                             raise (Fail "the name of set elements can't start with $")  
                                 else all_variables env prmlst stmt

and print_body set_name t_var var_name env prmlst = 
                               let var_t = (expr_to_string env prmlst t_var) in
              ("{\n"^(if(var_t="int")then "  RangeSet.RSIterator it = " else "  java.util.Iterator it = ")^(if(var_t="int")then "(RangeSet.RSIterator)"else " ")^(expr_to_string env prmlst set_name)^".iterator();\n  while(it.hasNext()){\n"^"  "^var_t^" "^(expr_to_string env prmlst var_name)^" ="^(if(var_t<>"int") then "("^(expr_to_string env prmlst t_var)^")" else " ")^"it.next();\n"^"  boolean test = (")

and print_filter set_name t_var var_name env prmlst = 
              ("{\n"^"  Set set = new HashSet();\n"^"  java.util.Iterator it = "^(expr_to_string env prmlst set_name)^".iterator();\n  while(it.hasNext()){\n"^"  "^ (expr_to_string env prmlst t_var)^" "^(expr_to_string env prmlst var_name)^" =("^(expr_to_string env prmlst t_var)^")it.next();\n"^"  boolean test = (")

and print_flt_rest var_name = ("  if(test){\n    set.add("^(expr_to_string [] [] var_name)^"); }\n  }\n"^"  return set;\n}\n*/\n")

and print_rch_rest p_list env prmlst = match p_list with
                 | h::tail -> let head = (expr_to_string env prmlst h) in 
                      "if("^head^"!=null&&set.add("^head^")){\nstack.push("^head^");\n}\n"^print_rch_rest tail env prmlst
                 | [] -> ""

and print_map set_name t_var var_name env prmlst = 
	      ("{\n"^"  Set set = new HashSet();\n"^"  java.util.Iterator it = "^(expr_to_string env prmlst set_name)^".iterator();\n  while(it.hasNext()){\n"^"  "^ (expr_to_string env prmlst t_var)^" "^(expr_to_string env prmlst var_name)^" =("^(expr_to_string env prmlst t_var)^")it.next();\n  "^(expr_to_string env prmlst t_var)^" test = (")

and print_map_rest var_name = ("  set.add(test); }\n  }\n"^"  return set;\n}\n*/\n")

and print_meth_call_prm p_list env prmlst = match p_list with
                 | [] -> ""
                 | x::[] -> (expr_to_string env prmlst x)
                 | head::tail -> (expr_to_string env prmlst head)^","^(print_meth_call_prm tail env prmlst)


 let _ =
	    output_string (open_out (Sys.argv.(1)^"_out")) ("");
            let lexbuf = Lexing.from_channel (open_in Sys.argv.(1)) in  
              let ast = ScParser.main ScLexer.token lexbuf in
                match ast with 
                   (all,exists,modifier,exp,p_list) -> all_suffix:= all; xst_suffix:= exists; 
                         if (modifier = "static") then static:="static";
			     let result = (expr_to_string [] p_list exp) in  
                       write (result^";\n"); write  ((string_of_int(!all_suffix)^"\n")); write (string_of_int(!xst_suffix)) 


