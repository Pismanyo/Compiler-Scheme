#use "tag-parser.ml";;
type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;	
                      
module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec find_major str lex_env index = match lex_env with
| [] -> -1
| hd :: tl -> if(List.mem str hd) then index
                                  else (find_major str tl index+1);;

let rec find_minor_index str l index = match l with
| hd :: tl -> if(str = hd) then index
                           else (find_minor_index str tl index+1)
| _ -> raise X_syntax_error;; 

let rec find_minor str lex_env = match lex_env with
| [] -> -1
| hd :: tl -> if(List.mem str hd) then (find_minor_index str hd 0)
                                       else (find_minor str tl);;
                                         
let handle_lex_var str lex_env params = if (List.mem str params) then VarParam(str, (find_minor_index str params 0))
                                                                 else (let str_major = (find_major str lex_env 0) in
                                                                       let str_minor = (find_minor str lex_env) in 
                                                                       if(str_major < 0 || str_minor < 0) then VarFree(str)
                                                                                                          else VarBound(str, str_major, str_minor))

let rec annotate_lex_addr e lex_env params = match e with
| Const(const) -> Const'(const)
| Var(str) -> Var'((handle_lex_var str lex_env params))
| If(test_expr, then_expr, else_expr) -> If'((annotate_lex_addr test_expr lex_env params), (annotate_lex_addr then_expr lex_env params), (annotate_lex_addr else_expr lex_env params))
| Seq(seq) -> Seq'((List.map (fun x -> (annotate_lex_addr x lex_env params)) seq))
| Set(var, value) -> (match var with 
                    | Var(str) -> Set'(((handle_lex_var str lex_env params)), (annotate_lex_addr value lex_env params))
                    | _ -> raise X_syntax_error)
| Def(var, value) -> (match var with
                    | Var(str) -> Def'((handle_lex_var str lex_env params), (annotate_lex_addr value lex_env params))
                    | _ -> raise X_syntax_error) 
| Or(expr_lst) -> Or'((List.map (fun x -> (annotate_lex_addr x lex_env params)) expr_lst))
| LambdaSimple(args, body) -> LambdaSimple'(args, (annotate_lex_addr body (params :: lex_env) args))
| LambdaOpt(args, optArgs, body) -> LambdaOpt'(args, optArgs, (annotate_lex_addr body (params :: lex_env) (args @ [optArgs])))
| Applic(rator, rands) -> Applic'((annotate_lex_addr rator lex_env params), (List.map (fun x-> (annotate_lex_addr x lex_env params)) rands))

let annotate_lexical_addresses e = (annotate_lex_addr e [] []);;

let rec annotate_tc e in_tp = match e with 
| Const' _ | Var' _ -> e
| If'(test_expr, then_expr, else_expr) -> If'((annotate_tc test_expr false), (annotate_tc then_expr in_tp), (annotate_tc else_expr in_tp))
| Seq'(seq) -> Seq'((annotate_tc_list seq in_tp))
| Set'(var, value) -> Set'(var, (annotate_tc value false))
| Def'(var, value) -> Def'(var, (annotate_tc value false))
| Or'(expr_lst) -> Or'((annotate_tc_list expr_lst in_tp))
| LambdaSimple'(args, body) -> LambdaSimple'(args, (annotate_tc body true))
| LambdaOpt' (args, optArgs, body) -> LambdaOpt'(args, optArgs, (annotate_tc body true))
| Applic' (rator, rands) -> if(in_tp) then ApplicTP'((annotate_tc rator false), (List.map (fun x -> (annotate_tc x false)) rands))
                                      else Applic'((annotate_tc rator false), (List.map (fun x -> (annotate_tc x false)) rands))
| _ -> raise X_syntax_error

and annotate_tc_list l in_tp = match l with
| [] -> []
| hd :: tl -> if(tl = []) then [(annotate_tc hd in_tp)]
                          else (annotate_tc hd false)::(annotate_tc_list tl in_tp);;

let annotate_tail_calls e = (annotate_tc e false);;

let raise_flag flag_ref = begin flag_ref:= true end;;

let should_box e varstr = let read_param_flag = ref false in
                          let write_param_flag = ref false in
                          let read_bound_flag = ref false in
                          let write_bound_flag = ref false in
                          let rec should_box_param e = match e with 
                          | Var'(VarParam(name, _)) -> if(varstr = name) then (begin (raise_flag read_param_flag); !write_bound_flag end)
                                                                         else false
                          | Const' _ | Var' _ -> false 
                          | If'(test_expr, then_expr, else_expr) -> (should_box_param test_expr) || (should_box_param then_expr) || (should_box_param else_expr)
                          | Seq'(seq) -> let (result, seq_write, seq_read) = (should_box_seq seq) in
                                         (begin read_bound_flag:= (!read_bound_flag || seq_read); write_bound_flag:= (!write_bound_flag || seq_write); result end)
                          | Set'(VarParam(varname, _), value) -> if(varname = varstr) then (begin (raise_flag write_param_flag); (!read_bound_flag || (should_box_param value)) end)
                                                                                      else (should_box_param value)
                          | Set'(_, value) -> (should_box_param value)
                          | Or'(expr_list) -> (List.fold_left (fun boolean exp -> boolean || (should_box_param exp)) false expr_list)
                          | LambdaSimple'(args, body) -> if(List.mem varstr args) then false
                                                                                else let (result, lambda_write, lambda_read) = (should_box_bound e) in
                                                                                     (begin read_bound_flag:= (!read_bound_flag || lambda_read); write_bound_flag:= (!write_bound_flag || lambda_write); result end)
                          | LambdaOpt'(args, optArgs, body) -> if(List.mem varstr (args@[optArgs])) then false
                                                                                      else let (result, lambda_write, lambda_read) = (should_box_bound e) in
                                                                                     (begin read_bound_flag:= (!read_bound_flag || lambda_read); write_bound_flag:= (!write_bound_flag || lambda_write); result end)
                          | Applic'(rator, rands) | ApplicTP'(rator, rands) -> (List.fold_left (fun boolean exp -> boolean || (should_box_param exp)) false (rator::rands))
                          | _ -> false
                          
                          and should_box_bound e = let write_flag = ref false in 
                                              let read_flag = ref false in
                                              let rec should_box_in_bound e = match e with
                          | Var'(VarBound(name, _, _)) -> if(varstr = name) then (begin (raise_flag read_flag); (!write_bound_flag || !write_param_flag) end)
                                                                            else false
                          | Const' _ | Var' _ -> false 
                          | If'(test_expr, then_expr, else_expr) -> (should_box_in_bound test_expr) || (should_box_in_bound then_expr) || (should_box_in_bound else_expr)
                          | Seq'(seq) -> (List.fold_left (fun boolean exp -> boolean || (should_box_in_bound exp)) false seq)
                          | Set'(VarBound(varname, _, _), value) -> if(varname = varstr) then (begin (raise_flag write_flag); (!read_bound_flag || !read_param_flag || (should_box_in_bound value)) end)
                                                                                      else (should_box_in_bound value)
                          | Set'(_, value) -> (should_box_in_bound value)
                          | Or'(expr_list) -> (List.fold_left (fun boolean exp -> boolean || (should_box_in_bound exp)) false expr_list)
                          | LambdaSimple'(args, body) -> if(List.mem varstr args) then false
                                                                                else (should_box_in_bound body)
                          | LambdaOpt'(args, optArgs, body) -> if(List.mem varstr (args@[optArgs])) then false
                                                                                      else (should_box_in_bound body)
                          | Applic'(rator, rands) | ApplicTP'(rator, rands) -> (List.fold_left (fun boolean exp -> boolean || (should_box_in_bound exp)) false (rator::rands)) 
                          | _ -> false in
                          let result = (should_box_in_bound e) in
                          (result, !write_flag, !read_flag)

                          and should_box_seq l = let write_flag = ref false in 
                                                 let read_flag = ref false in
                                                 let rec should_box_handle_seq e = match e with 
                          | Var'(VarParam(name, _)) -> if(varstr = name) then (begin (raise_flag read_flag); !write_bound_flag end)
                                                                         else false
                          | Set'(VarParam(varname, _), value) -> (match value with 
                                                                | LambdaSimple' _ | LambdaOpt' _ -> let (a, b, c) = (should_box_bound value) in
                                                                                                    let res = (a || b || c) in
                                                                       if(varname = varstr) then (begin (raise_flag write_flag); (!read_bound_flag || res) end)
                                                                                      else res
                                                                | _ -> let res = (should_box_param value) in 
                                                                       if(varname = varstr) then (begin (raise_flag write_flag); (!read_bound_flag || res) end)
                                                                                      else res)
                          | Const' _ | Var' _  | If' _ | Set' _ | Or' _ | LambdaSimple' _ | LambdaOpt' _ | Applic' _ | ApplicTP' _ -> (should_box_param e) 
                          | _ -> false
                          in
                          let result = (List.fold_left (fun boolean exp -> boolean || (should_box_handle_seq exp)) false l) in             
                          (result, !write_flag, !read_flag) in
                          (should_box_param e);;

let rec index_in_list var index l = match l with
| [] -> -1
| hd :: tl -> if(var = hd) then index
                           else (index_in_list var (index+1) tl);;

        
let rec replace_getset var_names body = match body with
| LambdaSimple'(args, body) ->if(List.exists (fun x -> (List.mem x var_names)) args) then LambdaSimple'(args, (replace_getset (List.filter (fun x -> (not (List.mem x args))) var_names) body))
                                                                                       else LambdaSimple'(args, (replace_getset var_names body))
| LambdaOpt'(args, optArgs, body) ->if(List.exists (fun x -> (List.mem x var_names)) (args@[optArgs])) then LambdaOpt'(args, optArgs, (replace_getset (List.filter (fun x -> (not (List.mem x (args@[optArgs])))) var_names) body))
                                                                                       else LambdaOpt'(args, optArgs, (replace_getset var_names body))                                                                                       
| Var'(VarParam(name, minor)) -> if(List.mem name var_names) then BoxGet'(VarParam(name, minor))
                                                             else body
| Var'(VarBound(name, major, minor)) -> if(List.mem name var_names) then BoxGet'(VarBound(name, major, minor))
                                                                    else body                                                          
| Set'(var, value) ->  (match var with
                       | VarParam(name, _) | VarBound(name, _, _) -> if(List.mem name var_names) then BoxSet'(var, (replace_getset var_names value))
                                                                                                 else body
                       | _ -> body)                                                                                                 
| If'(test_expr, then_expr, else_expr)-> If'((replace_getset var_names test_expr), (replace_getset var_names then_expr), (replace_getset var_names else_expr))
| Seq'(seq) -> Seq'((List.map (fun x -> (replace_getset var_names x)) seq))
| Or'(expr_list) -> Or'((List.map (fun x -> (replace_getset var_names x)) expr_list))
| Applic'(rator, rands) -> Applic'((replace_getset var_names rator), (List.map (fun x-> (replace_getset var_names x)) rands))
| ApplicTP'(rator, rands) -> ApplicTP'((replace_getset var_names rator), (List.map (fun x-> (replace_getset var_names x)) rands))
| _ -> body ;;

let handle_lambda_box e = match e with
| LambdaSimple'(args, body) -> let should_box_pair_list = (List.map (fun x -> (x, (should_box body x))) args) in
                               let args_to_box = (List.filter (fun x -> ((snd x) = true)) should_box_pair_list) in
                               let var_names = (List.map (fun x -> (fst x)) args_to_box) in
                               let var_params = (List.map (fun x -> VarParam((fst x), (index_in_list (fst x) 0 args))) args_to_box) in
                               let should_box_bools = (List.map (fun x -> (snd x)) should_box_pair_list) in
                               if(not (List.mem true should_box_bools)) then e
                                                                        else (let boxing_sets = (List.map (fun x -> Set'(x, Box'(x))) var_params) in
                                                                              let new_body = (replace_getset var_names body) in 
                                                                              let seq_sets_new_body = Seq'(boxing_sets@[new_body]) in
                                                                              LambdaSimple'(args, seq_sets_new_body)) 

| LambdaOpt'(args, optArgs, body) -> let should_box_pair_list = (List.map (fun x -> (x, (should_box body x))) (args@[optArgs])) in
                               let args_to_box = (List.filter (fun x -> ((snd x) = true)) should_box_pair_list) in
                               let var_names = (List.map (fun x -> (fst x)) args_to_box) in
                               let var_params = (List.map (fun x -> VarParam((fst x), (index_in_list (fst x) 0 (args@[optArgs])))) args_to_box) in
                               let should_box_bools = (List.map (fun x -> (snd x)) should_box_pair_list) in
                               if(not (List.mem true should_box_bools)) then e
                                                                        else (let boxing_sets = (List.map (fun x -> Set'(x, Box'(x))) var_params) in
                                                                              let new_body = (replace_getset var_names body) in 
                                                                              let seq_sets_new_body = Seq'(boxing_sets@[new_body]) in
                                                                              LambdaOpt'(args, optArgs, seq_sets_new_body))                                                                               
| _ -> raise X_syntax_error;;                                                                                                         
                          
let rec wrap_box e = match e with 
| BoxSet'(var, value) -> BoxSet'(var, (wrap_box value))
| If'(test_expr, then_expr, else_expr) -> If'((wrap_box test_expr), (wrap_box then_expr), (wrap_box else_expr))
| Seq'(seq) -> Seq'((List.map (fun x -> (wrap_box x)) seq))
| Set'(var, value) -> Set'(var, (wrap_box value))
| Def'(var, value) -> Def'(var, (wrap_box value))
| Or'(expr_list) -> Or'((List.map (fun x -> (wrap_box x)) expr_list))
| LambdaSimple'(args, body) -> let boxed_lambda = (handle_lambda_box e) in
                               (match boxed_lambda with 
                               | LambdaSimple'(args, new_body) -> LambdaSimple'(args, (wrap_box new_body))
                               | LambdaOpt'(args, optArgs, new_body) -> LambdaOpt'(args, optArgs, (wrap_box new_body))
                               | _ -> raise X_syntax_error)
| LambdaOpt'(args, optArgs, body) -> let boxed_lambda = (handle_lambda_box e) in
                               (match boxed_lambda with 
                               | LambdaSimple'(args, new_body) -> LambdaSimple'(args, (wrap_box new_body))
                               | LambdaOpt'(args, optArgs, new_body) -> LambdaOpt'(args, optArgs, (wrap_box new_body))
                               | _ -> raise X_syntax_error)
| Applic'(rator, rands) -> Applic'((wrap_box rator), (List.map (fun x -> (wrap_box x)) rands))
| ApplicTP'(rator, rands) -> ApplicTP'((wrap_box rator), (List.map (fun x -> (wrap_box x)) rands))
| _ -> e;;

let seq_splice l = let spliced_seq = (List.fold_left (fun acc cur -> match cur with
                                                                     | Seq'(seq) -> acc @ seq
                                                                     | _ -> acc @ [cur]) [] l) in
                                                                                 Seq'(spliced_seq);;

let rec flat_seq e = match e with 
| Seq'(seq) -> (seq_splice seq)
| BoxSet'(var, value) -> BoxSet'(var, (flat_seq value))
| If'(test_expr, then_expr, else_expr) -> If'((flat_seq test_expr), (flat_seq then_expr), (flat_seq else_expr))
| Set'(var, value) -> Set'(var, (flat_seq value))
| Def'(var, value) -> Def'(var, (flat_seq value))
| Or'(expr_list) -> Or'((List.map (fun x -> (flat_seq x)) expr_list))
| LambdaSimple'(args, body) -> LambdaSimple'(args, (flat_seq body))
| LambdaOpt'(args, optArgs, body) -> LambdaOpt'(args, optArgs, (flat_seq body))
| Applic'(rator, rands) -> Applic'((flat_seq rator), (List.map (fun x -> (flat_seq x)) rands))
| ApplicTP'(rator, rands) -> ApplicTP'((flat_seq rator), (List.map (fun x -> (flat_seq x)) rands))
| _ -> e;;

let box_set e = (flat_seq (wrap_box e));;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)


