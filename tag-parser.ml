#use "reader.ml";;
 
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec is_proper_list l = match l with 
| Nil -> true
| Pair(hd, tl) -> is_proper_list tl
| _ -> false;;

let rec sexpr_to_stringlist_proper sexpr = match sexpr with
| Nil -> []
| Pair(Symbol(hd), tl) -> hd :: (sexpr_to_stringlist_proper tl)
| _ -> raise X_syntax_error;;

let rec sexpr_to_stringlist_improper sexpr = match sexpr with
| Pair(Symbol(hd), Pair(second, tl)) -> hd :: (sexpr_to_stringlist_improper (Pair(second, tl)))
| Pair(Symbol(hd), tl) -> [hd]
| _ -> raise X_syntax_error;;

let symbol_to_string sym = match sym with
| Symbol(str) -> str 
| _ -> raise X_syntax_error;;

let rec last_in_imp_list l = match l with
| Pair(hd, tl) -> last_in_imp_list tl
| _ -> l;;

let rec vars_from_argslist l = match l with 
| Pair(Pair(Symbol(name), _), next) -> name :: (vars_from_argslist next)
| _ -> [];;

let mit_define_macro_expansion sexpr = match sexpr with
| Pair(Symbol("define"), Pair(Pair(var, args), body)) -> Pair(Symbol("define"), Pair(var, Pair(Pair(Symbol("lambda"), Pair(args, body)), Nil)))
| _ -> raise X_syntax_error;;

let rec quasiquote_macro_expansion sexpr = match sexpr with
| Pair(Symbol("unquote"), Pair(unquote_sexpr, Nil)) -> unquote_sexpr
| Pair(Symbol("unquote-splicing"), Pair(unquote_splicing_sexpr, Nil)) -> Pair(Symbol("quote"), Pair(sexpr, Nil))
| Nil | Symbol _ -> Pair(Symbol("quote"), Pair(sexpr, Nil))
| Pair(hd, tl) -> (match (hd, tl) with
                  | (Pair(Symbol("unquote-splicing"), Pair(unquote_splicing_sexp, Nil)), _) -> Pair(Symbol("append"), Pair(unquote_splicing_sexp, Pair((quasiquote_macro_expansion tl), Nil)))
                  | (_, _) -> Pair(Symbol("cons"), Pair((quasiquote_macro_expansion hd), Pair((quasiquote_macro_expansion tl), Nil))))
| exp -> Pair(Symbol("quote"), Pair(exp, Nil));;

let rec letrec_whatever_and_set args body = match args with
| Nil -> (Nil, body)
| Pair(Pair(arg, Pair(value, Nil)), restBinds) -> (match restBinds with 
                                                  | Nil -> let whateverArg = Pair(Pair(arg, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), Nil) in
                                                   let setArg = Pair(Pair(Symbol("set!"), Pair(arg, Pair(value, Nil))), body)
                                                   in (whateverArg, setArg)
                                                  | _ -> let (restWhatArgs, restSetArgs) = (letrec_whatever_and_set restBinds body) in
                                                         let whateverArg = Pair(Pair(arg, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), restWhatArgs) in
                                                         let setArg = Pair(Pair(Symbol("set!"), Pair(arg, Pair(value, Nil))), restSetArgs) in 
                                                        (whateverArg, setArg))                                                       
| _ -> raise X_syntax_error;; 

let letrec_macro_expansion args body = let (args, body) = (letrec_whatever_and_set args body) in 
  Pair(Symbol("let"), Pair(args, body));;
                                                      

let rec generateNewBinds args index = match args with
  | Nil -> (Nil, Pair(Pair(Symbol("begin"), Nil), Nil))
  | Pair(Pair(Symbol(var), Pair(value, Nil)), rest) -> let (binds, body) = (generateNewBinds rest (index+1)) in
                                                       let newVar = ";"^(string_of_int index) in
                                                       let bind = Pair(Symbol(newVar), Pair(value, Nil)) in
                                                       let bodyExp = Pair(Symbol("set!"), Pair(Symbol(var), Pair(Symbol(newVar), Nil))) in
                                                                    (Pair(bind, binds), Pair(bodyExp, body))
  | _ -> raise X_syntax_error;;                                                   



        let rec tag_parse_expression sexpr = match sexpr with
        | Bool _ | Char _ | Number _ | String _ -> Const(Sexpr sexpr)
        | Pair(Symbol("quote"), Pair(quoted_sexpr, Nil)) -> Const(Sexpr quoted_sexpr)
        | Symbol(str) -> if(List.mem str reserved_word_list) then raise X_syntax_error else Var(str)
        | Pair(Symbol("if"), Pair(test_expr, Pair(then_expr, Pair(else_expr, Nil)))) -> If(tag_parse_expression test_expr, tag_parse_expression then_expr, tag_parse_expression else_expr)
        | Pair(Symbol("if"), Pair(test_expr, Pair(then_expr, Nil))) -> If(tag_parse_expression test_expr, tag_parse_expression then_expr, Const(Void)) 
        | Pair(Symbol("lambda"), Pair(Symbol(arg), body)) -> LambdaOpt([], arg, (begin_tag_parse body))
        | Pair(Symbol("lambda"), Pair(args, body))-> if(is_proper_list args) then LambdaSimple((sexpr_to_stringlist_proper args), (begin_tag_parse body)) 
                                                                             else LambdaOpt((sexpr_to_stringlist_improper args), symbol_to_string(last_in_imp_list args), (begin_tag_parse body))
        | Pair(Symbol("or"), args) -> or_tag_parse args
        | Pair(Symbol("define"), Pair(Pair(var, args), body)) -> (tag_parse_expression (mit_define_macro_expansion sexpr))
        | Pair(Symbol("define"), Pair(var, Pair(value, Nil))) -> Def((tag_parse_expression var), (tag_parse_expression value))
        | Pair(Symbol("set!"), Pair(var, Pair(value, Nil))) -> Set((tag_parse_expression var), (tag_parse_expression value))
        | Pair(Symbol("begin"), body) -> (begin_tag_parse body)
        | Pair(Symbol("quasiquote"), Pair(quasi_sexpr, Nil)) -> (tag_parse_expression (quasiquote_macro_expansion quasi_sexpr))
        | Pair(Symbol("cond"), ribs) -> (tag_parse_expression (cond_macro_expansion ribs))
        | Pair(Symbol("let"), Pair(args, body)) -> (let_macro_expansion args body)
        | Pair(Symbol("let*"), Pair(args, body)) -> (tag_parse_expression (let_star_macro_expansion args body))
        | Pair(Symbol("letrec"), Pair(args, body)) -> (tag_parse_expression (letrec_macro_expansion args body))
        | Pair(Symbol("and"), args) -> (and_macro_expansion args)
        | Pair(Symbol("pset!"), args) -> (tag_parse_expression (pset_macro_expansion args))
        | Pair(rator, rands) -> Applic((tag_parse_expression rator), (proplist_to_exprlist rands))
        | _ -> raise X_syntax_error

     and begin_tag_parse body = match body with
     | Nil -> Const(Void)
     | Pair(hd, Nil) -> (tag_parse_expression hd)
     | Pair(hd, tl) -> (seq_splice hd tl)
     | _ -> raise X_syntax_error 

     and seq_splice hd tl = let expr_list = (proplist_to_exprlist (Pair(hd, tl))) in
                            let reduced = (List.fold_left (fun l expr -> match expr with 
                                                                        | Seq(seq_expr) -> l @ seq_expr
                                                                        | _ -> l @ [expr]) [] expr_list) in Seq(reduced)

     and proplist_to_exprlist l = match l with
     | Nil -> []
     | Pair(hd, tl) -> (tag_parse_expression hd) :: (proplist_to_exprlist tl)
     | _ -> raise X_syntax_error

     and or_tag_parse l = match l with
     | Nil -> Const(Sexpr(Bool(false)))
     | Pair(hd, Nil) -> (tag_parse_expression hd)
     | _ -> Or((proplist_to_exprlist l))

     and vals_from_argslist l = match l with 
     | Pair(Pair(Symbol(name), Pair(value, Nil)), next) -> (tag_parse_expression value) :: vals_from_argslist next
     | _ -> []

     and let_macro_expansion args body = Applic(LambdaSimple((vars_from_argslist args), (begin_tag_parse body)), (vals_from_argslist args))  

     and let_star_macro_expansion args body = match args with 
     | Nil | Pair(_, Nil) -> Pair(Symbol("let"), Pair(args, body))
     | Pair(hd, tl) -> Pair(Symbol("let"), Pair(Pair(hd, Nil), Pair((let_star_macro_expansion tl body), Nil)))
     | _ ->  raise X_syntax_error

     and cond_macro_expansion ribs = match ribs with
     | Nil -> Pair(Symbol("begin"), Nil)
     | Pair(Pair(Symbol("else"), elserib), restribs) -> (Pair(Symbol("begin"), elserib))
     | Pair(Pair(lhs_expr, Pair(Symbol("=>"), Pair(rhs_expr, Nil))), Nil) -> (Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(lhs_expr, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(rhs_expr, Nil), Nil))), Nil)), Nil)),
     Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil))))
     | Pair(Pair(lhs_expr, Pair(Symbol("=>"), Pair(rhs_expr, Nil))), restribs) -> (Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(lhs_expr, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(rhs_expr, Nil))), Nil)), Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair((cond_macro_expansion restribs), Nil))), Nil)), Nil))), 
     Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil))))
     | Pair(Pair(testexpr,thenexpr), Nil) ->  (Pair(Symbol("if"), Pair(testexpr, Pair(Pair(Symbol("begin"), thenexpr), Pair((cond_macro_expansion Nil), Nil)))))
     | Pair(Pair(testexpr, thenexpr), restribs) ->  (Pair(Symbol("if"), Pair(testexpr, Pair(Pair(Symbol("begin"), thenexpr), Pair((cond_macro_expansion restribs), Nil)))))
     | _ -> raise X_syntax_error

     and and_macro_expansion args = match args with
     | Nil -> Const(Sexpr(Bool(true)))
     | Pair(hd, Nil) -> (tag_parse_expression hd)
     | Pair(hd, tl) -> (tag_parse_expression (Pair(Symbol("if"), Pair(hd, Pair(Pair(Symbol("and"), tl), Pair(Bool(false), Nil))))))
     | _ -> raise X_syntax_error

     and pset_macro_expansion args =
          let (newBinds, body) = (generateNewBinds args 1) in
              Pair(Symbol("let"), Pair(newBinds, body));;

let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;

  
end;; (* struct Tag_Parser *)

