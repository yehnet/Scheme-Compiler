#use "reader.ml";;
(* open Reader;; *)


type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec list_to_pairs_of_vars lst =
  match lst with
  | [] -> ScmNil
  | hd::tl -> ScmPair(ScmSymbol(hd),list_to_pairs_of_vars tl)

let rec list_to_pairs lst =
  match lst with
  | [] -> ScmNil
  | hd::tl -> ScmPair(hd,list_to_pairs tl)

    
let rec flatten_pairs x = 
  match x with
  | ScmNil -> []
  | ScmPair(first,rest) -> first::(flatten_pairs rest)
  | s -> [s]

let rec is_proper_list x = 
  match x with
  | ScmNil -> true
  | ScmPair(_,ScmNil) -> true
  | ScmPair(first,rest) -> is_proper_list rest
  | _ -> false

let is_symbol x = 
  match x with
  | ScmSymbol(s) -> true
  | _ -> false

let rec take lst n = 
  match lst with
  | hd::tl -> if n=0 then [] else hd::(take tl (n-1))
  | [] -> []

let get_var_from_rib rib =
  match rib with 
  | ScmPair(ScmSymbol(var), _) -> var
  | _ -> raise X_not_implemented

let get_val_from_rib rib =
  (* let debug = (Printf.printf "%s" (string_of_sexpr rib)) in *)
  match rib with 
  | ScmPair(_,ScmPair(value,ScmNil)) -> value
  | ScmPair(_,value) -> value
  | _ -> raise X_not_implemented
  

  let extract_let_vars rib ribs = 
    let rib_var = get_var_from_rib rib in
    let ribs = flatten_pairs ribs in
    let ribs_vars = List.map get_var_from_rib ribs in
    let ribs_vars = rib_var::ribs_vars in
    list_to_pairs_of_vars ribs_vars

  let extract_let_vals rib ribs = 
    let rib_val = get_val_from_rib rib in
    let ribs = flatten_pairs ribs in
    let ribs_vals = List.map get_val_from_rib ribs in
    let ribs_vals = rib_val::ribs_vals in
    list_to_pairs ribs_vals

let make_whatever rib =
match rib with
| ScmPair(var,value) -> ScmPair(var, ScmPair(ScmSymbol("quote"),ScmPair(ScmSymbol("whatever"),ScmNil)))
| _ -> raise X_not_implemented

let rec make_whatever_pairs ribs=
  match ribs with
  | ScmNil -> ScmNil
  | ScmPair(rib, ScmNil) -> ScmPair((make_whatever rib), ScmNil)
  | ScmPair(rib,ribs) -> ScmPair((make_whatever rib),(make_whatever_pairs ribs))
  | _ -> raise X_not_implemented

let make_setbang rib = 
  match rib with
  | ScmNil -> ScmNil
  | ScmPair(var,value) -> ScmPair(ScmSymbol("set!"), ScmPair(var,value))
  | _ -> raise X_not_implemented

let rec make_setbang_pairs ribs =
  match ribs with
  | ScmNil -> ScmNil
  | ScmPair(rib, ScmNil) -> ScmPair((make_setbang rib), ScmNil)
  | ScmPair(rib, rest) -> ScmPair((make_setbang rib), (make_setbang_pairs rest))
  | _ -> raise X_not_implemented

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)
| ScmNil -> ScmConst(ScmVoid)
| ScmBoolean(x) -> ScmConst(ScmBoolean(x))
| ScmChar(x) -> ScmConst(ScmChar(x))
| ScmNumber(x) -> ScmConst(ScmNumber(x))
| ScmString(x) -> ScmConst(ScmString(x))
| ScmPair(ScmSymbol("quote"), ScmPair(x,ScmNil)) -> ScmConst(x)
| ScmSymbol(x) when (List.mem x reserved_word_list) -> raise (X_reserved_word x)
| ScmPair(ScmSymbol("if"), ScmPair(
  test, 
  ScmPair(dit, ScmPair(dif, ScmNil)))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
  | ScmPair(ScmSymbol("if"), ScmPair(test, 
    ScmPair(dit, ScmNil))) -> ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst(ScmVoid))
  (* Or *)
  | ScmPair(ScmSymbol("or"), ScmNil) -> ScmConst (ScmBoolean false)
  | ScmPair(ScmSymbol("or"), ScmPair(operand, ScmNil)) -> (tag_parse_expression operand)
  | ScmPair(ScmSymbol("or"), operands) -> ScmOr(List.map tag_parse_expression (flatten_pairs operands))
  | ScmPair(ScmSymbol("begin"), ScmPair(first, ScmNil)) -> tag_parse_expression first
  | ScmPair(ScmSymbol("begin"), sequence) -> ScmSeq(List.map tag_parse_expression (flatten_pairs sequence))
  (* Lambda *)
  | ScmPair(ScmSymbol("lambda"), ScmPair(arglist,exprs)) -> process_lambda arglist exprs
  (* define *)
  | ScmPair(ScmSymbol("define"), ScmPair(vars,value)) -> process_define vars value
  (* set! *)
  | ScmPair(ScmSymbol("set!"), ScmPair(ScmSymbol(var),ScmPair(value, ScmNil))) -> ScmSet(ScmVar(var),tag_parse_expression value)
  (* Reserved Word *)
  | ScmSymbol(x) when not (List.mem x reserved_word_list) -> ScmVar(x)
  (* Application *)
  | ScmPair(operator, operands) -> process_application operator operands
  
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and process_application f parameters =
ScmApplic((tag_parse_expression f), (List.map tag_parse_expression (flatten_pairs parameters)))
and process_lambda arglist exprs = 
  if is_proper_list arglist then
    (process_lambda_simple arglist exprs)
  else if (is_symbol arglist) then (process_variadic_lambda arglist exprs)
  else (process_lambda_opt arglist exprs)

and symbol_to_string sxpr = 
  match sxpr with 
  | ScmSymbol(x) -> x
  | _ -> raise X_not_implemented

and process_lambda_simple arglist exprs = 
  let arglist_flat = flatten_pairs arglist in
  let arglist_parsed = List.map symbol_to_string arglist_flat in
  let exprs_flat = flatten_pairs exprs in
  let exprs_parsed = List.map tag_parse_expression exprs_flat in
  if List.length exprs_flat > 1 then
    ScmLambdaSimple(arglist_parsed, ScmSeq(exprs_parsed))
  else 
    ScmLambdaSimple(arglist_parsed, (List.nth exprs_parsed 0))

and process_lambda_opt arglist exprs =
  let arglist_flat = flatten_pairs arglist in
  let last_arg = List.nth arglist_flat ((List.length arglist_flat) - 1) in
  let last_arg = symbol_to_string last_arg in
  let regular_args = take arglist_flat ((List.length arglist_flat) - 1) in
  let regular_args = List.map symbol_to_string regular_args in
  let exprs_flat = flatten_pairs exprs in
  let exprs_parsed = List.map tag_parse_expression exprs_flat in
  if (List.length exprs_flat) = 1 then 
    ScmLambdaOpt(regular_args, last_arg, (List.nth exprs_parsed 0))
  else
    ScmLambdaOpt(regular_args, last_arg, ScmSeq(exprs_parsed))

and process_variadic_lambda arglist exprs = 
  let exprs_flat = flatten_pairs exprs in
  let exprs_parsed = List.map tag_parse_expression exprs_flat in
  if (List.length exprs_flat) = 1 then 
    ScmLambdaOpt([],(symbol_to_string arglist),(List.nth exprs_parsed 0))
  else 
    ScmLambdaOpt([],(symbol_to_string arglist), ScmSeq(exprs_parsed))

and process_define var value =
(* check if regular define *)
match var,value with
| ScmSymbol(x),ScmPair(y,ScmNil) -> ScmDef(ScmVar(x), tag_parse_expression y)
| ScmPair(ScmSymbol(id), rest),value -> mit_lambda_define id rest value
| _ -> raise X_not_implemented

and mit_lambda_define id vars value = 
let lambda = process_lambda vars value in
ScmDef(ScmVar(id), lambda)

and handle_let rib ribs body =
let vars = extract_let_vars rib ribs in
let values = extract_let_vals rib ribs in
ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(vars,body)), values)

and handle_let_empty body =
let vars = ScmNil in
ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(vars,body)), ScmNil)


and handle_and operands =
match operands with
| ScmNil->ScmBoolean(true)
| ScmPair(op, ScmNil) -> op
| ScmPair(op, rest) -> ScmPair(ScmSymbol("if"), ScmPair(op, ScmPair(ScmPair(ScmSymbol("and"), rest), ScmPair(ScmBoolean(false),ScmNil))))
| _ -> raise X_not_implemented

and handle_let_star_empty body =
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))

and handle_let_star_base_1 rib r1 ribs body =
  macro_expand (ScmPair(ScmSymbol("let"),ScmPair(ScmPair(rib,ScmNil), (macro_expand (ScmPair(ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(r1,ribs), body)), ScmNil))))))

and handle_let_star rib ribs body = 
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib,ribs), body)))

(* and handle_letrec rib ribs body =
  let rib_whatever = make_whatever rib in
  let ribs_whatever = make_whatever_pairs ribs in
  let all_ribs_whatever = ScmPair(rib_whatever, ribs_whatever) in
  let rib_setbang = make_setbang rib in
  let ribs_setbang = make_setbang_pairs ribs in
  let all_ribs_setbang = ScmPair(rib_setbang, ribs_setbang) in
  let final_let = macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body))) in
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(all_ribs_whatever, ScmPair(all_ribs_setbang, final_let)))) *)

and handle_letrec list = 
  let rec getVars lst = match lst with 
    (* | ScmPair (ScmPair (s, x),ScmNil) -> ScmPair(s,ScmNil) *)
    | ScmPair (ScmPair (s, x),ScmNil) -> ScmPair(s,ScmNil)
    | ScmPair (ScmPair (s, x), rest) ->ScmPair (s, getVars rest)
    | ScmNil -> ScmNil
    | _ -> raise X_not_implemented
    in
  let rec whatever vars = match vars with
    | ScmPair(s,ScmNil) -> ScmPair(ScmPair (s, ScmPair(ScmPair(ScmSymbol "quote" , ScmPair (ScmSymbol "whatever",ScmNil)), ScmNil)),ScmNil)
    | ScmPair(ScmSymbol(s),x) ->  ScmPair(ScmPair(ScmSymbol(s), ScmPair(ScmPair(ScmSymbol "quote" , ScmPair (ScmSymbol "whatever",ScmNil)), ScmNil)), whatever x) 
    (* | ScmPair (s, x) -> ScmPair (whatever (ScmPair(s,ScmNil)), whatever x) *)
    | _ -> raise X_not_implemented
    in

  let rec sets varsVals seq= match varsVals with
    | ScmNil                    -> seq
    | ScmPair (ScmPair(s,x), rest) -> ScmPair(ScmPair(ScmSymbol "set!" , ScmPair(s, x)), sets rest seq)
    | _ -> raise X_not_implemented
    in
    match list with 
    | ScmPair ( varsVals, seq ) -> macro_expand (ScmPair (ScmSymbol "let" , ScmPair(whatever (getVars varsVals),sets varsVals seq)))
    | _ -> raise X_not_implemented

and handle_cond ribs  = 
match ribs with
| ScmNil -> ScmNil
| ScmPair(ScmPair(ScmSymbol("else"), body), rest) -> ScmPair(ScmSymbol("begin"), body)
| ScmPair(ScmPair(condition,ScmPair(ScmSymbol("=>"), body)),rest) -> let e1 = ScmPair(ScmSymbol("value"), condition) in
                                                                     let e2 = ScmPair(ScmSymbol("f"), ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, body))) in
                                                                     let e3 = ScmPair(ScmSymbol("rest"), ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair((handle_cond rest), ScmNil)))) in
                                                                     let let_body = ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"),ScmPair(ScmPair(ScmPair (ScmSymbol("f"), ScmNil),ScmPair (ScmSymbol("value"), ScmNil)),ScmPair (ScmPair (ScmSymbol("rest"), ScmNil), ScmNil)))) in
                                                                     macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(e1,ScmPair(e2,ScmPair(e3, ScmNil))), ScmPair(let_body,ScmNil))))

| ScmPair(ScmPair(condition, body), rest) -> ScmPair(ScmSymbol("if"), ScmPair(condition, ScmPair(ScmPair(ScmSymbol("begin"), body), ScmPair((handle_cond rest), ScmNil))))
| _ -> raise X_not_implemented


and handle_quasiquote expression =
match expression with
| ScmPair(ScmSymbol("unquote"), ScmPair(exp_rest,ScmNil)) -> exp_rest
| ScmPair(ScmSymbol("unquote-splicing"), ScmPair(exp_rest,ScmNil)) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("unquote-splicing"), exp_rest))
| ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(ScmNil,ScmNil))
| ScmSymbol(x) -> ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol(x),ScmNil))
| ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(a,ScmNil)), b) -> ScmPair(ScmSymbol("append"), ScmPair(a, ScmPair((handle_quasiquote b), ScmNil)))
| ScmPair(a, b) -> ScmPair(ScmSymbol("cons"), ScmPair((handle_quasiquote a), ScmPair((handle_quasiquote b), ScmNil)))
| ScmVector(list) -> handle_qq_vector list
| x -> x

and handle_qq_vector vector = 
let list_form = list_to_pairs vector in
let expanded = handle_quasiquote list_form in
ScmPair(ScmSymbol("list->vector"), ScmPair(expanded, ScmNil))

and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)) -> handle_let_empty body
| ScmPair(ScmSymbol("let"), ScmPair(ScmPair(rib, ribs), body)) -> handle_let rib ribs body
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil, body)) -> handle_let_star_empty body
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(rib, ScmPair(r1, ribs)), body)) -> handle_let_star_base_1 rib r1 ribs body
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(rib,ribs), body)) -> handle_let_star rib ribs body
| ScmPair(ScmSymbol("letrec"), ScmPair(ScmNil,body)) -> handle_let_star_empty body
| ScmPair(ScmSymbol("letrec"), list) -> handle_letrec list
| ScmPair(ScmSymbol("and"), operands) -> handle_and operands
| ScmPair(ScmSymbol("cond"), ribs) -> handle_cond ribs
| ScmPair(ScmSymbol("quasiquote"), ScmPair(expression, ScmNil)) -> handle_quasiquote expression
| _ -> sexpr
end;;