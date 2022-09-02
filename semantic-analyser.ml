(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

 #use "tag-parser.ml";;
 (* open Tparser.Tag_Parser *)

 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
 
 type var' = 
   | VarFree of string
   | VarParam of string * int
   | VarBound of string * int * int;;
 
 type expr' =
   | ScmConst' of sexpr
   | ScmVar' of var'
   | ScmBox' of var'
   | ScmBoxGet' of var'
   | ScmBoxSet' of var' * expr'
   | ScmIf' of expr' * expr' * expr'
   | ScmSeq' of expr' list
   | ScmSet' of var' * expr'
   | ScmDef' of var' * expr'
   | ScmOr' of expr' list
   | ScmLambdaSimple' of string list * expr'
   | ScmLambdaOpt' of string list * string * expr'
   | ScmApplic' of expr' * (expr' list)
   | ScmApplicTP' of expr' * (expr' list);;
 
 
 let var_eq v1 v2 =
 match v1, v2 with
   | VarFree (name1), VarFree (name2) -> String.equal name1 name2
   | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
     major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
   | VarParam (name1, index1), VarParam (name2, index2) ->
        index1 = index2 && (String.equal name1 name2)
   | _ -> false
 
 let rec expr'_eq e1 e2 =
   match e1, e2 with
   | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
   | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
   | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                             (expr'_eq dit1 dit2) &&
                                               (expr'_eq dif1 dif2)
   | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
         List.for_all2 expr'_eq exprs1 exprs2
   | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
         (var_eq var1 var2) && (expr'_eq val1 val2)
   | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
   | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
   | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
       (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
   | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
   | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
   | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
   | _ -> false;;
 
   let unannotate_lexical_address = function
   | (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name
   
   let rec unanalyze expr' =
   match expr' with
     | ScmConst' s -> ScmConst(s)
     | ScmVar' var -> unannotate_lexical_address var
     | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
     | ScmBoxGet' var -> unannotate_lexical_address var
     | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
     | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
     | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
     | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
     | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
     | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
     | ScmLambdaSimple' (params, expr') ->
           ScmLambdaSimple (params, unanalyze expr')
     | ScmLambdaOpt'(params, param, expr') ->
           ScmLambdaOpt (params, param, unanalyze expr')
     | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
           ScmApplic (unanalyze expr', List.map unanalyze expr's);;
   
   let string_of_expr' expr' =
       string_of_expr (unanalyze expr');;
 
 module type SEMANTIC_ANALYSIS = sig
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
   val run_semantics : expr -> expr'
 end;; (* end of module type SEMANTIC_ANALYSIS *)
 
 module Semantic_Analysis : SEMANTIC_ANALYSIS = struct
 
   let rec lookup_in_rib name = function
     | [] -> None
     | name' :: rib ->
        if name = name'
        then Some(0)
        else (match (lookup_in_rib name rib) with
              | None -> None
              | Some minor -> Some (minor + 1));;
 
   let rec lookup_in_env name = function
     | [] -> None
     | rib :: env ->
        (match (lookup_in_rib name rib) with
         | None ->
            (match (lookup_in_env name env) with
             | None -> None
             | Some(major, minor) -> Some(major + 1, minor))
         | Some minor -> Some(0, minor));;
 
   let tag_lexical_address_for_var name params env = 
     match (lookup_in_rib name params) with
     | None ->
        (match (lookup_in_env name env) with
         | None -> VarFree name
         | Some(major, minor) -> VarBound(name, major, minor))
     | Some minor -> VarParam(name, minor);;
 
   let rec getMinor var list idx = 
     match list with
     | [] -> -1
     | car::cdr -> if (car = var) then idx
                   else  getMinor var cdr (idx+1)
 
   let rec getMajor var list rest idx = 
     if (List.mem var list)
      then VarBound(var, idx, getMinor var list 0)
      else match rest with
          | [] -> VarFree(var)
          | car::rest -> getMajor var car rest (idx+1) 
 
   let whichVar var params env =
     let minorIdx = getMinor var params 0 in
     if ( minorIdx != -1)
      then VarParam(var,minorIdx)
      else
        match env with
        | [] -> VarFree(var)
        | car::rest -> (getMajor var car rest 0)
 
   (* run this first! *)
   let annotate_lexical_addresses pe = 
    let rec run pe params env =
       match pe with
       | ScmConst(pe) -> ScmConst'(pe)
       | ScmVar(var) ->  ScmVar'(whichVar var params env)
       | ScmIf(test,dit,dif) -> ScmIf'(run test params env, run dit params env, run dif params env)
       | ScmSet(ScmVar(a),v) -> ScmSet'(whichVar a params env,run v params env)
       | ScmDef(ScmVar(a),v) -> ScmDef'(whichVar a params env,run v params env)
       | ScmSeq(seq) -> ScmSeq'( List.map (fun(a) -> run a params env) seq)
       | ScmOr(ors) -> ScmOr'( List.map (fun(a) -> run a params env) ors)
       | ScmLambdaSimple(args,body) -> ScmLambdaSimple'(args, run body args (params::env))
       | ScmLambdaOpt(args, optArgs, body) -> ScmLambdaOpt'(args,optArgs, run body (args@[optArgs]) (params::env))
       | ScmApplic(func, args) -> ScmApplic'(run func params env,List.map (fun(a) -> run a params env) args )
       | _ -> raise X_this_should_not_happen
    in 
    run pe [] [];;
 
   let rec rdc_rac s =
     match s with
     | [e] -> ([], e)
     | e :: s ->
        let (rdc, rac) = rdc_rac s
        in (e :: rdc, rac)
     | _ -> raise X_this_should_not_happen;;
   
   (* run this second! *)
   let annotate_tail_calls pe =
    let rec run pe in_tail =
      match pe with
      | ScmConst'(e) -> pe
      | ScmVar'(var) -> pe
      | ScmIf'(test,dit,dif) -> ScmIf'( run test false, run dit in_tail, run dif in_tail)
      | ScmSet'(vr,vl) -> ScmSet'(vr, run vl false)
      | ScmDef'(vr,vl) -> ScmDef'(vr,run vl false)
      | ScmSeq'(seq) -> ScmSeq'(checkTail seq in_tail)
      | ScmOr'(ors) -> ScmOr'(checkTail ors in_tail)
      | ScmLambdaSimple'(args, body) -> ScmLambdaSimple'(args, run body true)
      | ScmLambdaOpt'(args, optArgs, body) -> ScmLambdaOpt'(args,optArgs,run body true)
      | ScmApplic'(func,args) -> checkApplic func args in_tail
      | _ -> raise X_this_should_not_happen
    
 
    and checkTail lst in_tail = 
      List.mapi (fun id exp -> if (id == (List.length lst) -1)
                                then run exp in_tail
                                else run exp false ) lst
    
    and checkApplic func args in_tail =
      if (in_tail)
        then ScmApplicTP'(run func false, (List.map (fun(a) -> run a false) args))
        else ScmApplic'(run func false, (List.map (fun(a) -> run a false) args)) 
    in 
    run pe false                            
      
 
   (* boxing *)
 
   let find_reads name enclosing_lambda expr = raise X_not_yet_implemented 
  
   let add_box_to_body v minor body =
    match body with
    | ScmSeq'(seq) -> ScmSeq'([ScmSet'(VarParam(v, minor), ScmBox'(VarParam(v,minor)))] @ seq)
    | nonseq -> ScmSeq'([ScmSet'(VarParam(v, minor), ScmBox'(VarParam(v,minor)))] @ [nonseq])
    
    let apply_to_var_minor p body = 
      let minor = (int_of_string (List.nth p 0)) in
      let v = List.nth p 1 in
      add_box_to_body v minor body
    
    let rec replace_vars_with_box body =
      match body with
      | ScmConst'(e) -> body
      | ScmVar'(VarFree(v)) -> body
      | ScmVar'(VarParam(v,minor)) -> ScmBoxGet'(VarParam(v,minor))
      | ScmVar'(VarBound(v,major,minonr)) -> ScmBoxGet'(VarBound(v,major,minonr))
      | ScmIf' (test,dit,dif) -> ScmIf'(replace_vars_with_box test, replace_vars_with_box dit, replace_vars_with_box dif)
      | ScmSet'(VarFree(v),value) -> ScmSet'(VarFree(v), (replace_vars_with_box value))
      | ScmSet'(VarParam(v,minor), value) -> ScmBoxSet'(VarParam(v,minor), (replace_vars_with_box value))
      | ScmSet'(VarBound(v,major,minor), value) -> ScmBoxSet'(VarBound(v,major,minor), (replace_vars_with_box value))
      | ScmSeq'(seq) -> ScmSeq'(List.map replace_vars_with_box seq)
      | ScmDef'(var, value) -> ScmDef'(var, replace_vars_with_box value)
      | ScmOr'(operands) -> ScmOr'(List.map replace_vars_with_box operands)
      | ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args, body)
      | ScmLambdaOpt'(args, optArgs, body) -> ScmLambdaOpt'(args, optArgs, body)
      | ScmApplic'(func,args) -> ScmApplic'(replace_vars_with_box func, (List.map replace_vars_with_box args))
      | ScmApplicTP'(func,args) -> ScmApplicTP'(replace_vars_with_box func, (List.map replace_vars_with_box args))
      | ScmBoxGet'(var) -> body
      | ScmBoxSet'(var,value) -> body
      | _ -> raise X_not_yet_implemented
    
    
    and add_boxes_to_body args body = 
      let replaced_body = replace_vars_with_box body in
      let vars_with_minors = (List.mapi (fun idx var -> [(string_of_int idx);var]) args) in
      let body_with_prefix = List.fold_left (fun p next -> apply_to_var_minor next p) replaced_body vars_with_minors in
      body_with_prefix

  
   let boxingLambda lambda = 
   match lambda with
   | ScmLambdaSimple'(args,body) -> ScmLambdaSimple'(args, (add_boxes_to_body args body))
   | ScmLambdaOpt'(args, optArgs, body) -> ScmLambdaOpt'(args, optArgs, add_boxes_to_body (args @ [optArgs]) body)
   | _ -> raise X_this_should_not_happen

   let rec box_set expr = 
    match expr with
    | ScmConst'(e) -> expr
    | ScmVar'(var) -> expr
    | ScmIf'(test,dit,dif) -> ScmIf'( box_set test, box_set dit,box_set dif)
    | ScmSet'(vr,vl) -> ScmSet'(vr, box_set vl)
    | ScmDef'(vr,vl) -> ScmDef'(vr,box_set vl)
    | ScmSeq'(seq) -> ScmSeq'(List.map (fun(a) -> box_set a) seq)
    | ScmOr'(ors) -> ScmOr'(List.map (fun(a) -> box_set a) ors)
    | ScmLambdaSimple'(args, body) -> boxingLambda (ScmLambdaSimple'(args, box_set body))
    | ScmLambdaOpt'(args, optArgs, body) -> boxingLambda (ScmLambdaOpt'(args,optArgs,box_set body))
    | ScmApplic'(func,args) -> ScmApplic'(box_set func, List.map (fun(a) -> box_set a) args )
    | ScmApplicTP'(func,args) -> ScmApplicTP'(box_set func, List.map (fun(a) -> box_set a) args )
    | _ -> raise X_this_should_not_happen

   let run_semantics expr =
     box_set
       (annotate_tail_calls
          (annotate_lexical_addresses expr))
 
 end;; (* end of module Semantic_Analysis *)
 