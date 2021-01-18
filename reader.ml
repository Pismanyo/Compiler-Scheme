
  #use "pc.ml";;
  exception X_not_yet_implemented;;
  exception X_this_should_not_happen;;

  type number =
    | Fraction of int * int
    | Float of float;;
    
  type sexpr =
    | Bool of bool
    | Nil
    | Number of number
    | Char of char
    | String of string
    | Symbol of string
    | Pair of sexpr * sexpr;;
  
  let rec sexpr_eq s1 s2 =
    match s1, s2 with
    | Bool(b1), Bool(b2) -> b1 = b2
    | Nil, Nil -> true
    | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
    | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
    | Char(c1), Char(c2) -> c1 = c2
    | String(s1), String(s2) -> s1 = s2
    | Symbol(s1), Symbol(s2) -> s1 = s2
    | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | _ -> false;;
  
  module Reader: sig
    val read_sexprs : string -> sexpr list
  end
  = struct
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
    (fun ch -> (ch = (lowercase_ascii ch)))
    s) then str
    else Printf.sprintf "|%s|" str;;
  
  let nt_Boolean = PC.disj (PC.pack (PC.word_ci "#t") (fun _ -> Bool true))
                           (PC.pack (PC.word_ci "#f") (fun _ -> Bool false));;
  
  let nt_StringMetaChar = PC.disj_list [(PC.pack (PC.word "\\r") (fun _ -> '\r')); 
                                        (PC.pack (PC.word "\\n") (fun _ -> '\n'));
                                        (PC.pack (PC.word "\\t") (fun _ -> '\t'));
                                        (PC.pack (PC.word "\\f") (fun _ -> '\012'));
                                        (PC.pack (PC.word "\\\\") (fun _ -> '\\'));
                                        (PC.pack (PC.word "\\\"") (fun _ -> '\"'))];;
  
  let nt_StringLiteralChar = PC.guard PC.nt_any (fun ch -> ch != '\\' && ch != '\"');;
  
  let nt_StringChar = PC.disj nt_StringMetaChar nt_StringLiteralChar;;
  
  let nt_String = let nt_DoubleQuote = PC.pack (PC.char '\"') (fun _-> ['"']) in
                                       PC.pack (PC.caten_list [nt_DoubleQuote; PC.star nt_StringChar; nt_DoubleQuote])
                                               (function
                                               | [_; charList; _] -> String(list_to_string charList)
                                               | _ -> raise PC.X_no_match);;
  
  
  
  
  let nt_CharPrefix = PC.word "#\\";;
  
  let nt_VisibleSimpleChar = PC.guard PC.nt_any (fun ch-> (int_of_char ch) > (int_of_char ' '));;
  
  let nt_NamedChar = PC.disj_list [(PC.pack (PC.word_ci "nul") (fun _ -> '\000')); 
                                   (PC.pack (PC.word_ci "newline") (fun _ -> '\n'));
                                   (PC.pack (PC.word_ci "return") (fun _ -> '\r'));
                                   (PC.pack (PC.word_ci "tab") (fun _ -> '\t'));
                                   (PC.pack (PC.word_ci "page") (fun _ -> '\012'));
                                   (PC.pack (PC.word_ci "space") (fun _ -> ' '))];;
  
  let nt_Char = PC.pack (PC.caten nt_CharPrefix (PC.disj nt_NamedChar nt_VisibleSimpleChar)) (fun (_,ch) -> Char(ch));;
  
  let nt_Digit = PC.range '0' '9';;
  
  let nt_Natural = PC.pack (PC.plus nt_Digit) (fun s-> int_of_string (list_to_string s));;
  
  let nt_Natural_floatPoint =  PC.pack (PC.plus nt_Digit) (fun s-> list_to_string s);;

  let nt_Sign = PC.pack (PC.maybe (PC.disj (PC.char '+') (PC.char '-'))) (function 
                        | Some('+') -> 1
                        | Some('-') -> -1
                        | None -> 1
                        | _ -> raise PC.X_no_match);;
  
  let nt_Integer = PC.pack (PC.caten nt_Sign nt_Natural) (fun (n1, n2) -> n1 * n2);;
  
  let rec gcd n1 n2 = if n1 = 0 then n2 else gcd (n2 mod n1) n1;;
  
  let nt_Fraction = PC.pack (PC.caten_list [nt_Sign; nt_Natural; PC.pack (PC.char '/') (fun ch-> int_of_char ch); nt_Natural]) (function
  | [sign; n1; _; n2] -> let n = (gcd n1 n2) in Fraction(sign * n1/n, n2/n)
  | _ -> raise PC.X_no_match);;
  
  
  let rec reduce_zeroes num_list = match num_list with
  | (e :: s) -> if (e != '0') then (List.rev (e :: s)) else reduce_zeroes s
  | [] -> [];;
  
  let nt_Float = PC.pack (PC.caten nt_Sign (PC.caten nt_Natural (PC.caten (PC.char '.') nt_Natural_floatPoint))) (function
  | (sign, (n1, (_, n2_str))) -> let list_num = List.rev (string_to_list n2_str) in
                   let new_n2 = "0." ^ (list_to_string (reduce_zeroes list_num)) in
                   Float (float_of_int sign *. (float_of_int n1 +. float_of_string new_n2)));;
  
  let nt_Scientific = PC.pack (PC.caten_list [ (PC.disj nt_Float (PC.pack (nt_Integer) (fun num->Fraction(num,1)))); PC.pack (PC.char_ci 'e') (fun ch -> Fraction (int_of_char ch, 1)); (PC.pack (nt_Integer) (fun num->Fraction(num,1)))])
   (function
   | [n1; _; n2] -> (match n1, n2 with 
    | Fraction (n11, _), Fraction (n21, _) -> Float ((float_of_int n11) *. (10.0 ** (float_of_int n21)))
    | Float (n12), Fraction (n22, _) -> Float (n12 *. (10.0 ** (float_of_int n22)))
    | _, _ -> raise PC.X_no_match)
   | _ -> raise PC.X_no_match);;
  
  let nt_Number = PC.pack (PC.disj_list [nt_Fraction; nt_Scientific; nt_Float; PC.pack (nt_Integer) (fun numnum -> Fraction (numnum, 1))]) (fun num -> Number(num));;
  
  let nt_Dot = PC.char '.';;
  let nt_SymbolCharNoDot = PC.disj_list [PC.range_ci 'a' 'z'; 
                                         PC.range '0' '9'; 
                                         PC.char '!'; 
                                         PC.char '$';
                                         PC.char '^';
                                         PC.char '-';
                                         PC.char '_';
                                         PC.char '=';
                                         PC.char '+';
                                         PC.char '<';
                                         PC.char '>';
                                         PC.char '?';
                                         PC.char '/';
                                         PC.char ':';
                                         PC.char '*'];;
  
  let nt_SymbolChar = PC.disj nt_SymbolCharNoDot nt_SymbolCharNoDot;;
  
  let nt_Symbol = PC.pack (PC.disj (PC.pack (PC.caten nt_SymbolChar (PC.plus nt_SymbolChar)) (fun (ch, char_list) -> ch :: char_list))
  (PC.pack (nt_SymbolCharNoDot) (fun ch -> [ch])))
   (fun char_list -> Symbol (String.lowercase_ascii (list_to_string char_list)));;
  
   let nt_WhiteSpace = PC.range '\000' ' ';;
  
  
   let nt_LineComment = PC.pack 
      (PC.caten (PC.char ';') (PC.caten (PC.star (PC.guard PC.nt_any (fun ch -> ch != '\n'))) (PC.maybe (PC.char '\n')))) 
                (fun(_,(list_of_char, _)) -> ' ');;
  
  
  
  
   let rec make_proper_list = function
   | hd :: tl -> Pair(hd, (make_proper_list tl))
   | _ -> Nil;;  
  
  
   let rec make_imprroper_list = function
   | [] -> Nil
   | hd :: [] -> Pair (hd, Nil)
   | hd :: tl :: [] -> Pair (hd, tl)
   | hd :: tl_list -> Pair (hd, make_imprroper_list tl_list);;
  
  let removeCommentOrWhiteSpaces nt1 nt2 nt3 =
     PC.pack (PC.caten (PC.pack (PC.caten nt1 nt3) 
             (fun (_, sexp) -> sexp)) nt2) 
                       (fun (sexp, _) -> sexp);;

  let rec nt_Sexpr l = 
    let nt_sexpr = 
      cleanSexpr (PC.disj_list ( 
                  [nt_Boolean; nt_Char; (PC.not_followed_by nt_Number nt_Symbol);     
                  nt_String; nt_Symbol; nt_List l;
                  nt_DottedList l; nt_Quoted l; nt_QuasiQuoted l;
                  nt_Unquoted l; nt_UnquoteAndSpliced l])) 
  in nt_sexpr l

  and nt_SexprComment l = (PC.pack (PC.caten (PC.word "#;") nt_Sexpr) (fun _ -> ' ')) 

  and nt_CommentOrWhiteSpaces l =
    PC.star (PC.disj_list ([ nt_WhiteSpace; nt_LineComment; nt_SexprComment l]))

  and cleanSexpr nt l = removeCommentOrWhiteSpaces (nt_CommentOrWhiteSpaces l) (nt_CommentOrWhiteSpaces l) nt l

  and nt_List l = 
    PC.pack (PC.caten (PC.char '(') (PC.caten (nt_CommentOrWhiteSpaces l) (PC.caten (PC.star nt_Sexpr) (PC.char ')')))) 
            (fun (_, (_, (sexp, _))) -> make_proper_list sexp)

  and nt_DottedList l = 
    PC.pack (PC.caten (PC.char '(') (PC.caten (PC.plus nt_Sexpr) (PC.caten (PC.char '.') 
            (PC.caten nt_Sexpr (PC.char ')'))))) (fun (_, (sexp_list, (_, (sexp, _))))-> make_imprroper_list (sexp_list @ [sexp]))

  and nt_Quoted l = 
    PC.pack (PC.caten (PC.char '\'') nt_Sexpr)
            (fun (_, sexp) -> Pair (Symbol ("quote") , Pair (sexp, Nil)))

  and nt_QuasiQuoted l = 
      PC.pack (PC.caten (PC.char '`') nt_Sexpr)
              (fun (_, sexp) -> Pair (Symbol ("quasiquote") , Pair (sexp, Nil)))

  and nt_Unquoted l = 
      PC.pack (PC.caten (PC.char ',') nt_Sexpr)
              (fun (_, sexp) -> Pair (Symbol ("unquote") , Pair (sexp, Nil)))

  and nt_UnquoteAndSpliced l = 
    PC.pack (PC.caten (PC.word ",@") nt_Sexpr)
            (fun (_, sexp) -> Pair (Symbol ("unquote-splicing") , Pair (sexp, Nil)));;


let read_sexprs string = 
            let sExpParsed = (PC.star nt_Sexpr) (string_to_list string) in
            match sExpParsed with 
            | (sExpList, []) -> sExpList
            | _ -> raise PC.X_no_match;;
end;; (* struct Reader *)
