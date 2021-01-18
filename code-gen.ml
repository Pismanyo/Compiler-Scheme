#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let rec extract_sexprs_from_expr' e l = match e with
  | Const'(sexpr) -> l @ [sexpr]
  | BoxSet'(var, value) -> (extract_sexprs_from_expr' value l)
  | If'(test_expr, then_expr, else_expr) -> (extract_sexprs_from_expr' test_expr l) @ (extract_sexprs_from_expr' then_expr []) @ (extract_sexprs_from_expr' else_expr [])
  | Seq'(seq) -> let sexpr_lst = (List.map (fun x -> (extract_sexprs_from_expr' x [])) seq) in
                 let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] sexpr_lst) in
                 (l @ flaten_lst)
  | Set'(var, value) -> (extract_sexprs_from_expr' value l)
  | Def'(var, value) -> (extract_sexprs_from_expr' value l)
  | Or'(expr_list) -> let sexpr_lst = (List.map (fun x -> (extract_sexprs_from_expr' x [])) expr_list) in
                      let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] sexpr_lst) in
                      (l @ flaten_lst)
  | LambdaSimple'(args, body) | LambdaOpt'(args, _, body) -> (extract_sexprs_from_expr' body l)
  | Applic'(rator, rands) | ApplicTP'(rator, rands) -> let sexpr_lst = (List.map (fun x -> (extract_sexprs_from_expr' x [])) (rator :: rands)) in
                                                       let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] (sexpr_lst)) in
                                                       (l @ flaten_lst)                            
  | _ -> l;;

  let extract_sexprs_from_expr'_list expr'_list = (List.fold_left (fun acc cur -> (acc @ cur)) [] (List.map (fun x -> (extract_sexprs_from_expr' x [])) expr'_list));;

  let rec sexprs_list_to_set l new_l = match l with
  | [] -> new_l
  | hd :: tl -> if(List.mem hd tl) then (sexprs_list_to_set tl new_l)
                                   else (sexprs_list_to_set tl (new_l @ [hd]));;

  let rec add_subs l = match l with 
  | [] -> []
  | hd :: tl -> (match hd with 
                | Sexpr(Symbol(str)) -> (Sexpr(String(str)) :: [hd]) @ (add_subs tl)
                | Sexpr(Pair(car, cdr)) -> ((add_subs [Sexpr(car); Sexpr(cdr)]) @ [hd]) @ (add_subs tl)
                | _ -> (hd :: (add_subs tl)));;
                
  let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

  let ascii_format str = match str with
                        | "" ->  "\"\"" 
                        | _ -> let ascii_list =(List.map (fun x -> (Char.code x)) (string_to_list str)) in
                               let ascii_strings_list = (List.map (fun x -> (string_of_int x)) ascii_list) in
                               (String.concat ", " ascii_strings_list);;

  let rec search_in_const_table sexpr table = match table with
  | [] -> raise X_syntax_error 
  | hd :: tl -> if((fst hd) = sexpr) then (fst (snd hd))
                                     else (search_in_const_table sexpr tl);;

  let rec create_cons_table l address table = match l with 
  | [] -> table
  | hd :: tl -> (match hd with
                | Sexpr(Number(Fraction(num, den))) -> (create_cons_table tl (address+17) (table @ [(hd, (address, (Printf.sprintf "%s%d%s%d%s" "MAKE_LITERAL_RATIONAL(" num "," den ")")))]))
                | Sexpr(Number(Float(float_num))) -> if(float_num -. (float_of_int (int_of_float float_num)) = 0.0) 
                                                        then (create_cons_table tl (address+9) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_FLOAT(" ^ (string_of_float float_num) ^ "0" ^ ")")))]))
                                                        else (create_cons_table tl (address+9) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_FLOAT(" ^ (string_of_float float_num) ^ ")")))]))
                | Sexpr(Char(ch)) -> (create_cons_table tl (address+2) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char ch)) ^ ")")))])) 
                | Sexpr(String(str)) -> (create_cons_table tl (address+9+(String.length str)) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_STRING " ^ (ascii_format str))))]))
                | Sexpr(Symbol(str)) -> (create_cons_table tl (address+9) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (search_in_const_table (Sexpr(String(str))) table)) ^ ")")))]))
                | Sexpr(Pair(car, cdr)) -> (create_cons_table tl (address+17) (table @ [(hd, (address, (Printf.sprintf "%s" "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int (search_in_const_table (Sexpr(car)) table)) ^ 
                                                                                                                                        ", const_tbl+" ^ (string_of_int (search_in_const_table (Sexpr(cdr)) table)) ^ ")")))]))
                | _ -> (create_cons_table tl address table));;

  let rec extract_fvars_from_expr' e table = match e with
  | Var'(VarFree(var)) -> (table @ [var])
  | BoxSet'(var, value) -> (extract_fvars_from_expr' value table)
  | If'(test_expr, then_expr, else_expr) -> table @ (extract_fvars_from_expr' test_expr []) @ (extract_fvars_from_expr' then_expr []) @ (extract_fvars_from_expr' else_expr [])
  | Seq'(seq) -> let fvar_lst = (List.map (fun x -> (extract_fvars_from_expr' x [])) seq) in
                 let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] fvar_lst) in
                 (table @ flaten_lst)
  | Set'(var, value) -> table @ (extract_fvars_from_expr' (Var'(var)) []) @ (extract_fvars_from_expr' value [])
  | Def'(var, value) -> table @ (extract_fvars_from_expr' (Var'(var)) []) @ (extract_fvars_from_expr' value [])
  | Or'(expr_list) -> let fvar_lst = (List.map (fun x -> (extract_fvars_from_expr' x [])) expr_list) in
                      let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] fvar_lst) in
                      (table @ flaten_lst)
  | LambdaSimple'(args, body) | LambdaOpt'(args, _, body) -> (extract_fvars_from_expr' body table)
  | Applic'(rator, rands) | ApplicTP'(rator, rands) -> let fvar_lst = (List.map (fun x -> (extract_fvars_from_expr' x [])) (rator :: rands)) in
                                                       let flaten_lst = (List.fold_left (fun acc cur -> (acc @ cur)) [] (fvar_lst)) in
                                                       (table @ flaten_lst)                            
  | _ -> table;;

  let extract_fvars_from_expr'_list l = (List.fold_left (fun acc cur -> (acc @ cur)) [] (List.map (fun x -> (extract_fvars_from_expr' x [])) l));;
                                      
  let rec create_fvar_tbl l index table = match l with
  | [] -> table
  | hd :: tl -> if(List.mem hd tl) then (create_fvar_tbl tl index table)
                                   else (create_fvar_tbl tl (index+8) (table @ [(hd, index)]));;

  let rec search_in_fvar_table name table = match table with
  | [] -> -1
  | hd :: tl -> if((fst hd) = name) then (snd hd)
                                    else (search_in_fvar_table name tl);;
  let label_counter = ref 0;;
let label_num () = 
  let increment() = label_counter := !label_counter + 1 in
                     (begin increment(); !label_counter end);;

  let rec generate_code const_table fvar_table e env_size = match e with 
  | Def' (VarFree(name), value) -> (generate_code const_table fvar_table value env_size) ^ 
                                   "mov qword[fvar_tbl+" ^ (string_of_int (search_in_fvar_table name fvar_table)) ^ "], rax\n" ^
                                   "mov rax, SOB_VOID_ADDRESS\n" 
  | Const'(const) -> "mov rax, const_tbl+" ^ (string_of_int (search_in_const_table const const_table)) ^ "\n"
  | Var'(var) -> (match var with
                 | VarParam(_, minor) -> "mov rax, qword[rbp+8*(4+" ^ (string_of_int minor) ^ ")]\n"
                 | VarBound(_, major, minor) -> "mov rax, qword[rbp+8*2]\n" ^
                                                 "mov rax, qword[rax+8*" ^ (string_of_int major) ^ "]\n" ^
                                                 "mov rax, qword[rax+8*" ^ (string_of_int minor) ^ "]\n"
                 | VarFree(name) ->  "mov rax, qword[fvar_tbl+" ^ (string_of_int (search_in_fvar_table name fvar_table)) ^ "]\n")
  | Set'(var, value) -> (match var with 
                 | VarParam(_, minor) -> (generate_code const_table fvar_table value env_size) ^ 
                                          "mov qword[rbp+8*(4+" ^ (string_of_int minor) ^ ")], rax\n" ^
                                          "mov rax, SOB_VOID_ADDRESS\n"
                 | VarBound(_, major, minor) -> (generate_code const_table fvar_table value env_size) ^ 
                                                 "mov rbx, qword[rbp+8*2]\n" ^
                                                 "mov rbx, qword[rbx+8*" ^ (string_of_int major) ^ "]\n" ^ 
                                                 "mov qword[rbx+8*" ^ (string_of_int minor) ^ "], rax\n" ^
                                                 "mov rax, SOB_VOID_ADDRESS\n"
                 | VarFree(name) -> (generate_code const_table fvar_table value env_size) ^
                                     "mov qword[fvar_tbl+" ^ (string_of_int (search_in_fvar_table name fvar_table)) ^ "], rax\n" ^
                                     "mov rax, SOB_VOID_ADDRESS\n")
  | Seq'(seq) -> (String.concat "" (List.map (fun x -> (generate_code const_table fvar_table x env_size)) seq))
  | Or'(expr_list) -> let current_label = (string_of_int (label_num())) in
                      (String.concat ("cmp rax, SOB_FALSE_ADDRESS\n" ^ "jne Lexit" ^ current_label ^ "\n") (List.map (fun x -> (generate_code const_table fvar_table x env_size)) expr_list)) ^
                      "Lexit" ^ current_label ^ ":\n"
  
  | If'(test_expr, then_expr, else_expr) -> let current_label = (string_of_int (label_num ())) in
                                            (generate_code const_table fvar_table test_expr env_size) ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^ "je Lelse" ^ current_label ^ "\n" ^
                                            (generate_code const_table fvar_table then_expr env_size) ^ "jmp Lexit" ^ current_label ^ "\nLelse" ^ current_label ^ ":\n" ^
                                            (generate_code const_table fvar_table else_expr env_size) ^ "Lexit" ^ current_label ^ ":\n"
  | Box'(VarParam(_, minor)) -> "mov rax, qword[rbp+8*(4+" ^ (string_of_int minor) ^ ")]\n" ^ "MALLOC rbx, 8\n" ^ "mov [rbx], rax\n" ^ "mov rax, rbx\n" 
  | BoxGet'(var) -> (generate_code const_table fvar_table (Var'(var)) env_size) ^ "mov rax, qword[rax]\n"
  | BoxSet'(var, value) -> (generate_code const_table fvar_table value env_size) ^ "push rax\n" ^ (generate_code const_table fvar_table (Var'(var)) env_size) ^ "pop qword[rax]\n" ^ "mov rax, SOB_VOID_ADDRESS\n"
  | LambdaSimple'(args, body) -> (generate_code_lambda_simple args body const_table fvar_table (env_size)) 
  | LambdaOpt'(args, optArgs, body) -> (generate_code_lambda_opt (args @ [optArgs]) body const_table fvar_table (env_size))
  | Applic'(rator, rands) -> (generate_code_applic rator rands const_table fvar_table env_size)
  | ApplicTP'(rator, rands) -> (generate_code_applicTP rator rands const_table fvar_table env_size)
  | _ -> raise X_syntax_error                                    
                                           
  
  and generate_code_lambda_simple args body const_table fvar_table env_size = let current_label = (string_of_int (label_num ())) in
                                                "EXTEND_ENV " ^ (string_of_int env_size) ^ "\n" ^ 
                                                "mov rbx, rax\n" ^
                                                "MAKE_CLOSURE(rax, rbx, Lcode" ^ current_label ^ ")\n" ^
                                                "jmp Lcont" ^ current_label ^ "\n" ^
                                                "Lcode" ^ current_label ^ ":\n" ^
                                                "push rbp\n" ^
                                                "mov rbp,rsp\n" ^ 
                                                (generate_code const_table fvar_table body (env_size + 1)) ^
                                                "leave\n" ^ 
                                                "ret\n" ^
                                                "Lcont" ^ current_label ^ ":\n"

  and generate_code_lambda_opt args body const_table fvar_table env_size = let current_label = (string_of_int (label_num ())) in
                                                "EXTEND_ENV " ^ (string_of_int env_size) ^ "\n" ^ 
                                                "mov rbx, rax\n" ^
                                                "MAKE_CLOSURE(rax, rbx, Lcode" ^ current_label ^ ")\n" ^
                                                "jmp Lcont" ^ current_label ^ "\n" ^
                                                "Lcode" ^ current_label ^ ":\n" ^
                                                "ADJUST_STACK " ^ (string_of_int (List.length args)) ^ "\n" ^ 
                                                "push rbp\n" ^
                                                "mov rbp,rsp\n" ^ 
                                                (generate_code const_table fvar_table body (env_size + 1)) ^
                                                "leave\n" ^ 
                                                "ret\n" ^
                                                "Lcont" ^ current_label ^ ":\n"
                                              
  and generate_code_applic rator rands const_table fvar_table env_size = let reverse_rands = (List.rev rands) in
                                                                         let rands_code_list = (List.map (fun x -> (generate_code const_table fvar_table x env_size) ^ "push rax\n") reverse_rands) in
                                                                         let rands_string_code = (List.fold_left (fun acc cur -> (acc ^ cur)) "" rands_code_list) in
                                                                         let arg_count_push = ("push " ^ (string_of_int (List.length rands)) ^ "\n") in
                                                                         let code_gen_proc = (generate_code const_table fvar_table rator env_size) in
                                                                         let pushenv_callcode = "CLOSURE_ENV rbx, rax\n" ^ "push rbx\n" ^ "CLOSURE_CODE rbx, rax\n" ^ "call rbx\n" in
                                                                         let after_return = "add rsp, WORD_SIZE\n" ^ "pop rbx\n" ^ "shl rbx, 3\n" ^ "add rsp, rbx\n" in
                                                                         (rands_string_code ^ arg_count_push ^ code_gen_proc ^ pushenv_callcode ^ after_return)

  and generate_code_applicTP rator rands const_table fvar_table env_size = let reverse_rands = (List.rev rands) in
                                                                           let rands_code_list = (List.map (fun x -> (generate_code const_table fvar_table x env_size) ^ "push rax\n") reverse_rands) in
                                                                           let rands_string_code = (List.fold_left (fun acc cur -> (acc ^ cur)) "" rands_code_list) in
                                                                           let arg_count_push = ("push " ^ (string_of_int (List.length rands)) ^ "\n") in
                                                                           let code_gen_proc = (generate_code const_table fvar_table rator env_size) in
                                                                           let pushenv = "CLOSURE_ENV rbx, rax\n" ^ "push rbx\n" in
                                                                           let push_old_addr = "push qword[rbp + WORD_SIZE]\n" in 
                                                                           let fix_stack_string = "FIX_STACK_TP " ^ (string_of_int (3 + (List.length rands))) ^ "\n" in
                                                                           let jmpcode = "CLOSURE_CODE rbx, rax\n" ^ "jmp rbx\n" in
                                                                           (rands_string_code ^ arg_count_push ^ code_gen_proc ^ pushenv ^ push_old_addr ^ fix_stack_string ^ jmpcode);;                                                

  let initial_const_tbl = [(Void, (0, "db T_VOID"));
                           (Sexpr(Nil), (1, "db T_NIL"));
                           (Sexpr(Bool false), (2, "db T_BOOL, 0"));
                           (Sexpr(Bool true), (4, "db T_BOOL, 1"))];; 

  let prims = ["boolean?"; "flonum?"; "rational?"; "pair?"; "null?"; "char?"; "string?"; "procedure?"; "symbol?";
               "string-length"; "string-ref"; "string-set!"; "make-string"; "symbol->string"; "char->integer";
               "integer->char"; "exact->inexact"; "eq?"; "+"; "*"; "/"; "="; "<"; "numerator"; "denominator";
               "gcd"; "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!"];;

  let make_consts_tbl asts = let sexprs_list = (extract_sexprs_from_expr'_list asts) in
                             let sexprs_set = (List.rev (sexprs_list_to_set (List.rev sexprs_list) [])) in
                             let sexprs_with_subs = (add_subs sexprs_set) in
                             let sexprs_with_subs_set = (List.rev (sexprs_list_to_set (List.rev sexprs_with_subs) [])) in
                             (create_cons_table sexprs_with_subs_set 6 initial_const_tbl);;

  let make_fvars_tbl asts = (create_fvar_tbl (prims @ (sexprs_list_to_set (extract_fvars_from_expr'_list asts) [])) 0 []);;

  let generate consts fvars e = (generate_code consts fvars e 0);;
end;;

