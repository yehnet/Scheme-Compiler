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
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

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
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen (*: CODE_GEN *)= struct
  exception Miro of expr' * string;;
  (* ----------------------------------------------consts table------------------------------------------------------------------------------ *)
   let rec scan_consts lst scmExp =
    match scmExp with
    | ScmConst'(c) -> lst@[c]
    | ScmVar'(v) -> lst
    | ScmBox'(v) -> lst
    | ScmBoxSet'(v, exp) -> scan_consts lst exp
    | ScmBoxGet'(v) -> lst
    | ScmSet'(v, exp) -> scan_consts lst exp
    | ScmDef'(v, exp) -> scan_consts lst exp
    | ScmOr'(ors) -> List.flatten (List.map (fun x -> (scan_consts lst x)) ors)
    | ScmIf'(test, dif, dit) -> (scan_consts lst test) @ (scan_consts lst dif) @ (scan_consts lst dit)
    | ScmSeq'(seq) -> List.flatten (List.map (fun x -> scan_consts lst x) seq)
    | ScmLambdaSimple'(args, body) -> scan_consts lst body
    | ScmLambdaOpt'(args,argsOpt,body) -> scan_consts lst body
    | ScmApplic'(op, seq) -> (scan_consts lst op) @ List.flatten (List.map (fun x -> scan_consts lst x) seq)
    | ScmApplicTP'(op, seq) -> (scan_consts lst op) @ List.flatten (List.map (fun x -> scan_consts lst x) seq)
    (* | _ -> raise (Miro (scmExp, "blah"));; *)

(*
  let rec listToSet lst set =
    match lst with 
      | [] -> set
      | car::cdr -> if (List.mem car set) 
                      then (listToSet cdr set) 
                      else (listToSet cdr (set @ [car]));;

  let scan_sub_consts = raise X_not_yet_implemented;; *)
  let rec rem_dups lst = match lst with
  | [] -> []
  | car::cdr -> if (List.mem car cdr) 
                then (rem_dups cdr) 
                else [car] @ (rem_dups cdr)
  
  let remove_duplicates lst = 
  (* Reverse the list so that the last duplicate will be removed rather than the first*)
  (* This is due to rem_dups removing the first occurance in a duplicate *)
  let lst = List.rev lst in
  let result_rev = rem_dups lst in 
  List.rev result_rev
  (* create a 3-tuple: 
    1) The address of the constant sexpr
    2) The constant sexpr itself
    3) The representation of the constant sexpr as a list of bytes
  *)
  let rec expand_sexpr exp = 
    match exp with
    | ScmSymbol(s) -> [ScmString(s)] @ [exp]
    | ScmPair(car,cdr) -> (expand_sexpr car) @ (expand_sexpr cdr) @ [ScmPair(car,cdr)]
    (* | ScmVector(lst) -> (List.flatten (List.map (fun x-> (expand_sexpr x)) lst)) @ [ScmVector(lst)] *)
    | _ -> [exp]
  
  let rec make_vector_string str elements =
    match elements with
    | car::[] -> str^car
    | car::cdr -> (make_vector_string (str^"const_tbl+"^car^",") cdr)
    | _ -> raise X_not_yet_implemented;;
  
  let str_to_numbers str = (String.concat "," (List.map (fun x -> string_of_int (int_of_char x)) (string_to_list str)))

  let rec makeTriosTuples_pass_1 lst offset = 
    match lst with 
    | [] -> []
    | ScmNil::cdr -> [(ScmNil,(offset, "db T_NIL"))] @ (makeTriosTuples_pass_1 cdr (offset+1))
    | ScmVoid::cdr -> [(ScmVoid, (offset, "db T_VOID"))] @ (makeTriosTuples_pass_1 cdr (offset+1))
    | ScmBoolean(x)::cdr -> if x=true then [(ScmBoolean(x), (offset, "db T_BOOL, 1"))] @ (makeTriosTuples_pass_1 cdr (offset+2))
                                      else [(ScmBoolean(x), (offset, "db T_BOOL, 0"))] @ (makeTriosTuples_pass_1 cdr (offset+2))
    | ScmNumber(ScmRational(a,b))::cdr -> [( (ScmNumber(ScmRational(a,b))), (offset, "MAKE_LITERAL_RATIONAL("^(string_of_int a)^","^(string_of_int b)^")"))] @ (makeTriosTuples_pass_1 cdr (offset+17))
    | ScmNumber(ScmReal(a))::cdr -> [(ScmNumber(ScmReal(a)),(offset, "db T_FLOAT\n dq "^(string_of_float a)))] @ (makeTriosTuples_pass_1 cdr (offset+9))
    | ScmChar(c)::cdr -> [(ScmChar(c),(offset, "db T_CHAR, "^(string_of_int (int_of_char c))))] @ (makeTriosTuples_pass_1 cdr (offset+2))
    | ScmString(str)::cdr -> [(ScmString(str),(offset, "MAKE_LITERAL_STRING "^(str_to_numbers str)))] @ (makeTriosTuples_pass_1 cdr (offset+1+8+(String.length str)))
    (* | ScmVector(elements) -> (offset, ScmVector(elements), "MAKE_LITERAL_VECTOR("^(string_of_int (List.length elements))^","^) *)
    | ScmPair(a,b)::cdr -> [(ScmPair(a,b),(offset, "PLACEHOLDER"))] @ (makeTriosTuples_pass_1 cdr (offset+17))
    | ScmSymbol(s)::cdr -> [(ScmSymbol(s),(offset, "PLACEHOLDER"))] @ (makeTriosTuples_pass_1 cdr (offset+9))
    | _ -> raise X_not_yet_implemented
 
  let rec get_const_offset x lst = 
    match lst with
    | [] -> raise X_this_should_not_happen
    | (sexpr,(offset,  _))::cdr -> if sexpr=x then (string_of_int offset) else (get_const_offset x cdr)

  let make_pair_asm_string a b lst =
    "MAKE_LITERAL_PAIR(const_tbl+"^(get_const_offset a lst)^", const_tbl+"^(get_const_offset b lst)^")"
  
  let make_string_asm_string s lst =
    "MAKE_LITERAL_SYMBOL(const_tbl+"^(get_const_offset (ScmString(s)) lst)^")"

  let handle_symbol_and_pair x lst =
    match x with
    | (ScmPair(a,b),(offset , _)) -> (ScmPair(a,b), (offset, (make_pair_asm_string a b lst)))
    | (ScmSymbol(s),(offset, _)) -> (ScmSymbol(s), (offset, (make_string_asm_string s lst)))
    | _ -> x
  let tuples_pass_2 lst = List.map (fun x-> (handle_symbol_and_pair x lst)) lst 

    
    let make_consts_tbl asts = 
    let consts = List.flatten (List.map (fun x -> (scan_consts [ScmVoid; ScmNil;ScmBoolean(true);ScmBoolean(false)] x)) asts) in
    let consts = remove_duplicates consts in
    let consts_expanded = List.flatten (List.map expand_sexpr consts) in
    let consts_expanded = remove_duplicates consts_expanded in
    let tuples_pass_1 = makeTriosTuples_pass_1 consts_expanded 0 in
    let pass_2 = tuples_pass_2 tuples_pass_1 in
    pass_2


  (* let make_consts_tbl asts =
    let constsList = List.flatten (List.map (fun a -> scan_consts [] a) asts) in
    let constsSet = listToSet constsList [] in
    let subConsts =  scan_sub_consts constsSet in
    let constSet =  listToSet subConsts [] in 
    makeTriosTuples_pass_1 constSet 0 [] ;; *)

  (* ----------------------------------------------free variables table---------------------------------------------------------------------- *)
  let rec scan_fvars lst scmExp = 
    match scmExp with 
    | ScmConst'(x) -> []
    | ScmVar'(VarFree(lbl)) -> lst @ [lbl]
    | ScmVar'(v) -> lst
    | ScmBox'(VarFree(lbl)) -> lst @ [lbl]
    | ScmBox'(v) -> lst
    | ScmBoxSet'(VarFree(lbl), exp) -> scan_fvars (lst @ [lbl]) exp
    | ScmBoxSet'(v,exp) -> scan_fvars lst exp
    | ScmBoxGet'(VarFree(lbl)) -> lst @ [lbl]
    | ScmBoxGet'(v) -> lst
    | ScmSet'(VarFree(lbl), exp) -> scan_fvars (lst @ [lbl]) exp
    | ScmSet'(v,exp) -> scan_fvars lst exp
    | ScmDef'(VarFree(lbl), exp) -> scan_fvars (lst @ [lbl]) exp
    | ScmOr'(ors) -> List.flatten (List.map (fun x -> (scan_fvars lst x)) ors)
    | ScmIf'(test,dif,dit) -> (scan_fvars lst test) @ (scan_fvars lst dif) @ (scan_fvars lst dit)
    | ScmSeq'(seq) -> List.flatten (List.map (fun x -> (scan_fvars lst x)) seq)
    | ScmLambdaSimple'(args, body) -> scan_fvars lst body
    | ScmLambdaOpt'(args,optArgs,body) -> scan_fvars lst body
    | ScmApplic'(op, seq) -> (scan_fvars lst op) @ List.flatten (List.map (fun x -> (scan_fvars lst x)) seq)
    | ScmApplicTP'(op, seq) -> (scan_fvars lst op) @ List.flatten (List.map (fun x -> (scan_fvars lst x)) seq)
    | _ -> raise (Miro (scmExp,"error"))
  
  let print_fvar_list lst = 
    List.map (fun x -> (Printf.printf "%s" (string_of_expr' x))) lst

  
  let make_fvars_tbl asts = 
    let fvarsList = List.flatten ( List.map (fun a -> scan_fvars [] a) asts) in 
    let fvarsSet = remove_duplicates fvarsList in
    List.mapi (fun index label -> (label , index)) fvarsSet ;;

  let getFvarLabel var fvarTbl =
  (string_of_int (List.assoc var fvarTbl))

  let new_label_num x = (begin (x:=!x+1) ; !x end);;
  let label_index = ref 0;;
  (* ----------------------------------------------code generation--------------------------------------------------------------------------- *)
  let rec genAssembly constTbl fvTable nestCount e = 
    (* let debug = raise (Miro (e, "blah")) in *)
    match e with
| ScmConst'(c) -> begin
                match c with
                 | ScmVoid -> "mov rax, const_tbl+0\n"
                 | s -> "mov rax, "^"const_tbl+"^(get_const_offset s constTbl)^"\n";
                end

| ScmVar'(VarParam(_,minor)) -> "mov rax, qword[rbp+8*(4+"^(string_of_int minor)^")]\n"

| ScmSet'(VarParam(_,minor),e) ->  let minorString = (string_of_int minor) in
                                  (genAssembly constTbl fvTable nestCount e)^
                                  "\n"^"mov qword[rbp+8*(4+"^minorString^")],rax\n"^
                                  "mov rax, SOB_VOID_ADDRESS\n"

| ScmVar'(VarBound(_,major,minor)) ->  let majorString = (string_of_int major) in
                                    let minorString = (string_of_int minor) in
                                    "mov rax, qword[rbp+8*2]\n"^
                                    "mov rax, qword[rax+8*"^majorString^"]\n"^
                                    "mov rax, qword[rax+8*"^minorString^"]\n"

| ScmSet'(VarBound(_,major,minor),e) ->
                                       let majorString = (string_of_int major) in
                                       let minorString = (string_of_int minor) in
                                       (genAssembly constTbl fvTable nestCount e)^"\n"^
                                       "mov rbx, qword[rbp+8*2]\n"^
                                       "mov rbx, qword[rbx+8*"^majorString^"]\n"^
                                       "mov qword[rbx+8*"^minorString^"], rax\n"^
                                       "mov rax, SOB_VOID_ADDRESS\n"

| ScmVar'(VarFree(v)) ->  let fvarLabel = getFvarLabel v (fvTable) in
                       "mov rax, qword[fvar_tbl+8*"^fvarLabel^"]\n"

| ScmSet'(VarFree(v),e) -> let fvarLabel = getFvarLabel v (fvTable) in
                          (genAssembly constTbl fvTable nestCount e)^"\n"^
                          "mov qword[fvar_tbl+8*"^fvarLabel^"], rax\n"^
                          "mov rax, SOB_VOID_ADDRESS\n"

| ScmSeq'(l) ->  let seqAssemblyGen totalString e = totalString^(genAssembly constTbl fvTable nestCount e)^"\n" in
                 List.fold_left seqAssemblyGen "" l;

| ScmOr'(l) ->  let labelnum = (string_of_int (new_label_num label_index)) in
                let orAssemblyGen totalString e = totalString^(genAssembly constTbl fvTable nestCount e)^"\n"^"cmp rax, SOB_FALSE_ADDRESS\n"^"jne Lexit_"^labelnum^"\n" in
                let retStr = List.fold_left orAssemblyGen "" l in
                retStr^"Lexit_"^labelnum^":\n"

| ScmIf'(x,y,z) ->  let labelnum = (string_of_int (new_label_num label_index)) in
                 (genAssembly constTbl fvTable nestCount x)^"\n"^
                 "cmp rax, SOB_FALSE_ADDRESS\n"^
                 "je Lelse_"^labelnum^"\n"^
                 (genAssembly constTbl fvTable nestCount y)^"\n"^
                 "jmp Lexit_"^labelnum^"\n"^
                 "Lelse_"^labelnum^":\n"^
                 (genAssembly constTbl fvTable nestCount z)^"\n"^
                 "Lexit_"^labelnum^":\n";

| ScmBox'(v) -> ((genAssembly constTbl fvTable nestCount (ScmVar'(v))))^"\n"^
                "MALLOC rbx, 8\n"^
                "mov qword[rbx], rax\n"^
                "mov rax, rbx\n"

| ScmBoxGet'(v) -> (genAssembly constTbl fvTable nestCount (ScmVar'(v)))^"\n"^
                   "mov rax, qword[rax]\n"

| ScmBoxSet'(v,e) ->  (genAssembly constTbl fvTable nestCount e)^"\n"^
                      "push rax\n"^
                      (genAssembly constTbl fvTable nestCount (ScmVar'(v)))^"\n"^
                      "pop qword[rax]"^"\n"^
                      "mov rax, SOB_VOID_ADDRESS";


| ScmLambdaSimple'(args,body)-> let labelnum = (string_of_int (new_label_num label_index)) in
                                (* "COPY_ENV 8*("^((string_of_int (nestCount+1)))^") ,"^(string_of_int nestCount)^"\n"^
                                "mov rax, r10\n
                                mov rbx, qword[rbp+8*3] ;; rbx=argnum\n"^
                                "inc rbx\n
                                imul rbx, 8\n
                                MALLOC r10, rbx\n
                                mov qword[rax], r10\n
                                mov rdx, rbp\n
                                add rdx, 8*4\n
                                mov rbx, qword[rbp+8*3]\n
                                cmp rbx, 0\n
                                jne .cpy_"^labelnum^"\n
                                mov qword[r10], SOB_NIL_ADDRESS
                                jmp .make_closure_"^labelnum^"\n
                                .cpy_"^labelnum^":\n
                                cmp rbx, 0\n
                                je .make_closure_"^labelnum^"\n
                                mov rcx, qword[rdx]\n
                                mov qword[r10], rcx\n
                                add rdx, 8\n
                                add r10, 8\n
                                sub rbx, 1\n
                                jmp .cpy_"^labelnum^"\n
                                .make_closure_"^labelnum^":\n
                                mov r11, rax\n
                                MAKE_CLOSURE(rax, r11, .Lcode_"^labelnum^")\n
                                jmp Lcont_"^labelnum^"\n"^
                                ".Lcode_"^labelnum^":\n"^
                                "push rbp\n"^
                                "mov rbp, rsp\n"^
                                (genAssembly constTbl fvTable (nestCount+1) body)^"\n"^
                                "leave\n
                                ret\n
                                Lcont_"^labelnum^":\n" *)
                               "
                              ;;create extended environment
                              .extend_env_"^labelnum^":\n
                              MALLOC r10, 8*"^(string_of_int (nestCount+1))^"\n
                              mov r11, r10\n
                              add r11, 8\n
                              mov rcx, "^(string_of_int nestCount)^"\n
                              mov r12, qword[rbp+8*2] ;;r12=original-env\n
                              .copyloop"^labelnum^":\n
                              cmp rcx, 0
                              je .aftercopy"^labelnum^"\n

                              mov r13, qword[r12] \n
                              mov qword[r11], r13 ;;copy-vector-to-new-env\n
                              add r11, 8
                              add r12, 8
                              dec rcx
                              jmp .copyloop"^labelnum^"\n
                              .aftercopy"^labelnum^": \n
                              ;;allocate the amount of params
                              mov rbx, qword[rbp+8*3]
                              imul rbx, 8
                              
                              cmp rbx, 0
                              jne .copy_params_"^labelnum^"
                              MALLOC r13, 8
                              mov qword[r10], r13
                              jmp .make_closure_"^labelnum^"\n
                              .copy_params_"^labelnum^":
                              MALLOC r11, rbx
                              ;;copy params off the stack
                              mov rbx, qword[rbp+8*3]
                              mov rcx, 0    ;;rcx=base index
                                            ;;rbx=target index
                              cmp rbx, 0
                              je .make_closure_"^labelnum^"\n
                              .copy_2_"^labelnum^":\n
                              cmp rbx, rcx
                              je .aftercopy_2_"^labelnum^"\n
                              mov r12, qword[rbp+8*(4+rcx)]
                              mov qword[r11+8*rcx], r12
                              inc rcx
                              jmp .copy_2_"^labelnum^"\n
                              .aftercopy_2_"^labelnum^":\n
                              mov qword[r10], r11
                              .make_closure_"^labelnum^":\n
                              MAKE_CLOSURE(rax, r10, Lcode_"^labelnum^")\n
                              jmp Lcont_"^labelnum^"\n
                              Lcode_"^labelnum^":
                              push rbp
                              mov rbp, rsp
                              "^ (genAssembly constTbl fvTable (nestCount+1) body)^
                              "
                              leave \n
                              ret \n
                              Lcont_"^labelnum^":\n"

   


|ScmLambdaOpt'(args,opt,body)-> let labelnum = (string_of_int (new_label_num label_index)) in
                             let args_num = (List.length args) in
                            "
                          ;;create extended environment
                          extend_env_"^labelnum^":\n
                          MALLOC r10, 8*"^(string_of_int (nestCount+1))^"\n
                          mov r11, r10\n
                          add r11, 8\n
                          mov rcx, "^(string_of_int nestCount)^"\n
                          mov r12, qword[rbp+8*2] ;;r12=original-env\n
                          .copyloop"^labelnum^":\n
                          cmp rcx, 0
                          je .aftercopy"^labelnum^"\n

                          mov r13, qword[r12] \n
                          mov qword[r11], r13 ;;copy-vector-to-new-env\n
                          add r11, 8
                          add r12, 8
                          dec rcx
                          jmp .copyloop"^labelnum^"\n
                          .aftercopy"^labelnum^": \n
                          ;;allocate the amount of params
                          mov rbx, qword[rbp+8*3]
                          imul rbx, 8
                          
                          cmp rbx, 0
                          jne .copy_params_"^labelnum^"
                          MALLOC r13, 8
                          mov qword[r10], r13
                          jmp .make_closure_"^labelnum^"\n
                          .copy_params_"^labelnum^":
                          MALLOC r11, rbx
                          ;;copy params off the stack
                          mov rbx, qword[rbp+8*3]
                          mov rcx, 0    ;;rcx=base index
                                        ;;rbx=target index
                          cmp rbx, 0
                          je .make_closure_"^labelnum^"\n
                          .copy_2_"^labelnum^":\n
                          cmp rbx, rcx
                          je .aftercopy_2_"^labelnum^"\n
                          mov r12, qword[rbp+8*(4+rcx)]
                          mov qword[r11+8*rcx], r12
                          inc rcx
                          jmp .copy_2_"^labelnum^"\n
                          .aftercopy_2_"^labelnum^":\n
                          mov qword[r10], r11
                          .make_closure_"^labelnum^":\n
                          MAKE_CLOSURE(rax, r10, Lcode_"^labelnum^")\n
                          jmp Lcont_"^labelnum^"\n
                            Lcode_"^labelnum^":\n"^
                            "push rbp\n"^
                            "mov rbp, rsp\n"^
                            "mov rax, qword[rbp+8*3] ;;rax = argnum\n"^

                            ".make_list_opt_"^labelnum^":\n"^
                            
                            "mov rcx, rax\n"^
                            "sub rcx, "^(string_of_int args_num)^";;rcx = num_of_opt_args\n"^
                            "mov r14, rcx;;store num_of_opt_args for later use\n"^
                            "mov r10, "^(string_of_int args_num)^" ;;r10 = mandatory_argnum \n"^
                            "cmp r10, rax\n"^
                            "je .empty_opt_args_"^labelnum^"\n"^
                            "mov rbx, rcx\n"^
                            "mov rdx, rcx\n
                             add rdx, r10 \n
                             mov rax, qword[rbp+8*(4+rdx-1)]\n"^
                            "MAKE_PAIR(r11, rax, SOB_NIL_ADDRESS)
                             mov r15, r11 ;;store pair in r15\n "^
                            
                            "sub rcx, 1\n
                             cmp rcx, 0\n
                             je .store_arglist"^labelnum^"\n"^

                            ".cpy_loop_"^labelnum^":\n"^
                            "mov rdx, rcx\n
                             add rdx, r10 \n
                             mov rax, qword[rbp+8*(4+rdx-1)]\n"^
                            "MAKE_PAIR(r11, rax,r15)\n
                             mov r15, r11\n
                             loop .cpy_loop_"^labelnum^"\n"^
                             "mov qword[rbp+8*(4+r10)], r15 ;;store final list above mandatory args\n"^
                             "mov r13, r10\n"^
                             "add r13, 4\n"^
                             "add r13, 1\n"^
                             "sub r14, 1 ;; r14 = num_of_opt_args - 1\n"^
                             "SHIFT_FRAME r13, r14\n"^
                             "imul r14, 8\n"^
                             "add rsp, r14\n
                              add rbp, r14\n"^
                            "jmp .gen_body_"^labelnum^"\n"^

                            ".empty_opt_args_"^labelnum^":\n"^
                            "SHIFT_FRAME_DOWN\n"^
                            "mov rax, SOB_NIL_ADDRESS\n"^
                            "mov qword[rbp+8*(4+r10)], rax\n"^
                            "jmp .gen_body_"^labelnum^"\n"^

                            ".store_arglist"^labelnum^":\n"^
                            "mov qword[rbp+8*(4+r10)], r15 ;;store final list above mandatory args\n"^

                            ".gen_body_"^labelnum^":\n"^
                            "mov rax,"^(string_of_int args_num)^"\n
                             add rax, 1\n
                             mov qword[rbp+8*3], rax ;; argnum = argnum + 1\n"^

                            (genAssembly constTbl fvTable (nestCount+1) body)^"\n"^
                            "leave\n
                            ret\n
                            Lcont_"^labelnum^":\n"
                          

                            (* ";;create extended environment
                            .extend_env_"^labelnum^":\n
                            MALLOC r10, 8*"^(string_of_int (nestCount+1))^"\n
                            mov r11, r10\n
                            add r11, 8\n
                            mov rcx, "^(string_of_int nestCount)^"\n
                            mov r12, qword[rbp+8*2] ;;r12=original-env\n
                            .copyloop"^labelnum^":\n
                            cmp rcx, 0
                            je .aftercopy"^labelnum^"\n

                            mov r13, qword[r12] \n
                            mov qword[r11], r13 ;;copy-vector-to-new-env\n
                            add r11, 8
                            add r12, 8
                            dec rcx
                            jmp .copyloop"^labelnum^"\n
                            .aftercopy"^labelnum^": \n
                            ;;allocate the amount of params
                            mov rbx, qword[rbp+8*3]
                            imul rbx, 8
                            
                            cmp rbx, 0
                            jne .copy_params_"^labelnum^"
                            MALLOC r13, 8
                            mov qword[r10], r13
                            jmp .make_closure_"^labelnum^"\n
                            .copy_params_"^labelnum^":
                            MALLOC r11, rbx
                            ;;copy params off the stack
                            mov rbx, qword[rbp+8*3]
                            mov rcx, 0    ;;rcx=base index
                                          ;;rbx=target index
                            cmp rbx, 0
                            je .make_closure_"^labelnum^"\n
                            .copy_2_"^labelnum^":\n
                            cmp rbx, rcx
                            je .aftercopy_2_"^labelnum^"\n
                            mov r12, qword[rbp+8*(4+rcx)]
                            mov qword[r11+8*rcx], r12
                            inc rcx
                            jmp .copy_2_"^labelnum^"\n
                            .aftercopy_2_"^labelnum^":\n
                            mov qword[r10], r11
                            .make_closure_"^labelnum^":\n
                            MAKE_CLOSURE(rax, r10, .Lcode_"^labelnum^")\n
                            jmp Lcont_"^labelnum^"\n"^

                            ".Lcode_"^labelnum^":\n"^
                            "push rbp\n"^
                            "mov rbp, rsp\n"^
                            "mov rax, qword[rbp+8*3] ;;rax = argnum\n"^

                            ".make_list_opt_"^labelnum^":\n"^

                            "mov rcx, rax\n"^
                            "sub rcx, "^(string_of_int args_num)^";;rcx = num_of_opt_args\n"^
                            "mov r14, rcx;;store num_of_opt_args for later use\n"^
                            "mov r10, "^(string_of_int args_num)^" ;;r10 = mandatory_argnum \n"^
                            "cmp r10, rax\n"^
                            "je .empty_opt_args_"^labelnum^"\n"^
                            "mov rbx, rcx\n"^
                            "mov rdx, rcx\n
                             add rdx, r10 \n
                             mov rax, qword[rbp+8*(4+rdx-1)]\n"^
                            "MAKE_PAIR(r11, rax, SOB_NIL_ADDRESS)
                             mov r15, r11 ;;store pair in r15\n "^

                            "sub rcx, 1\n
                             cmp rcx, 0\n
                             je .store_arglist"^labelnum^"\n"^

                            ".cpy_loop_"^labelnum^":\n"^
                            "mov rdx, rcx\n
                             add rdx, r10 \n
                             mov rax, qword[rbp+8*(4+rdx-1)]\n"^
                            "MAKE_PAIR(r11, rax,r15)\n
                             mov r15, r11\n
                             loop .cpy_loop_"^labelnum^"\n"^
                             "mov qword[rbp+8*(4+r10)], r15 ;;store final list above mandatory args\n"^
                             "mov r13, r10\n"^
                             "add r13, 4\n"^
                             "add r13, 1\n"^
                             "sub r14, 1 ;; r14 = num_of_opt_args - 1\n"^
                             "SHIFT_FRAME r13, r14\n"^
                             "imul r14, 8\n"^
                             "add rsp, r14\n
                              add rbp, r14\n"^
                            "jmp .gen_body_"^labelnum^"\n"^

                            ".empty_opt_args_"^labelnum^":\n"^
                            "SHIFT_FRAME_DOWN\n"^
                            "mov rax, SOB_NIL_ADDRESS\n"^
                            "mov qword[rbp+8*(4+r10)], rax\n"^
                            "jmp .gen_body_"^labelnum^"\n"^

                            ".store_arglist"^labelnum^":\n"^
                            "mov qword[rbp+8*(4+r10)], r15 ;;store final list above mandatory args\n"^

                            ".gen_body_"^labelnum^":\n"^
                            "mov rax,"^(string_of_int args_num)^"\n
                             add rax, 1\n
                             mov qword[rbp+8*3], rax ;; argnum = argnum + 1\n"^

                            (genAssembly constTbl fvTable (nestCount+1) body)^"\n"^
                            "leave\n
                            ret\n
                            Lcont_"^labelnum^":\n" *)

| ScmApplic'(proc, arglist) -> let labelnum = (string_of_int (new_label_num label_index)) in
                            let args_rev = (List.rev arglist) in
                            let argnum = (List.length arglist) in
                            let rec applicExpander args = match args with
                            | [] -> "jmp applic"^labelnum^"
                                    applic"^labelnum^": ;;this useless jmp is for debugging\n
                                    push "^(string_of_int argnum)^"\n"^
                                    (genAssembly constTbl fvTable nestCount proc)^"\n"^
                                    "mov rdx, rax\n"^ (* store proc address *)
                                    "cmp byte[rax],T_CLOSURE \n"^ (* make sure proc is closure *)
                                    "je .finish_"^labelnum^"\n"^
                                    ".not_closure_"^labelnum^":\n"^
                                    "mov rdi, not_closure_error_msg\n" ^
                                    "push rax\n"^
                                    "mov rax, 0\n"^
                                    "call printf\n"^
                                    "pop rax\n"^
                                    "jmp .after_applic_"^labelnum^"\n"^
                                    ".finish_"^labelnum^":\n"^
                                    "push qword[rax+TYPE_SIZE]\n"^ (* push env *)
                                    "call qword[rax + TYPE_SIZE+WORD_SIZE]\n"^
                                    "add rsp , 8*1 ; pop env\n"^
                                    "pop rbx ; pop arg count\n"^
                                    "shl rbx , 3 ; rbx = rbx * 8\n"^
                                    "add rsp , rbx; pop args\n"^
                                    ".after_applic_"^labelnum^":\n"

                            | arg :: rest -> (genAssembly constTbl fvTable nestCount arg)^
                                              "push rax\n"^
                                              (applicExpander rest) in
                              (applicExpander args_rev)

| ScmApplicTP'(proc, arglist) ->  let labelnum = (string_of_int (new_label_num label_index)) in
                            let args_rev = (List.rev arglist) in
                            let argnum = (List.length arglist) in
                            let rec applicExpander args = match args with
                            (* | [] -> "jmp applicTP"^labelnum^"
                                    applicTP"^labelnum^": ;;this useless jmp is for debugging\n
                                    push "^(string_of_int argnum)^"\n"^
                                    (genAssembly constTbl fvTable nestCount proc)^"\n"^
                                    "mov rdx, rax\n"^ (* store proc address *)
                                    "cmp byte[rax],T_CLOSURE \n"^ (* make sure proc is closure *)
                                    "je .finish_"^labelnum^"\n"^
                                    ".not_closure_"^labelnum^":\n"^
                                    "mov rdi, not_closure_error_msg\n" ^
                                    "push rax\n"^
                                    "mov rax, 0\n"^
                                    "call printf\n"^
                                    "pop rax\n"^
                                    "jmp .after_applic_"^labelnum^"\n"^
                                    ".finish_"^labelnum^":\n"^
                                    "push qword[rax+TYPE_SIZE]\n
                                    ;;fixing the stack\n
                                     push qword[rbp + 8]\n
                                     ;push qword[rbp]
                                     mov r8, qword[rbp+8*3]\n
                                     add r8, 4\n
                                     SHIFT_FRAME "^(string_of_int (argnum+3))^", r8 \n
                                     mov r9, "^(string_of_int (argnum+3))^"\n
                                     sub r8, r9
                                     shl r8, 3
                                     add r8, rbp
                                     ;add r9, 8
                                     mov rsp, r8
                                     ;mov rbp, rsp
                                     jmp qword[rax+TYPE_SIZE+WORD_SIZE]\n"^
                                    ".after_applic_"^labelnum^":\n" *)
                                    | [] -> "jmp applic"^labelnum^"
                                    applic"^labelnum^": ;;this useless jmp is for debugging\n
                                    push "^(string_of_int argnum)^"\n"^
                                    (genAssembly constTbl fvTable nestCount proc)^"\n"^
                                    "mov rdx, rax\n"^ (* store proc address *)
                                    "cmp byte[rax],T_CLOSURE \n"^ (* make sure proc is closure *)
                                    "je .finish_"^labelnum^"\n"^
                                    ".not_closure_"^labelnum^":\n"^
                                    "mov rdi, not_closure_error_msg\n" ^
                                    "push rax\n"^
                                    "mov rax, 0\n"^
                                    "call printf\n"^
                                    "pop rax\n"^
                                    "jmp .after_applic_"^labelnum^"\n"^
                                    ".finish_"^labelnum^":\n"^
                                    "push qword[rax+TYPE_SIZE]\n"^ (* push env *)
                                    "call qword[rax + TYPE_SIZE+WORD_SIZE]\n"^
                                    "add rsp , 8*1 ; pop env\n"^
                                    "pop rbx ; pop arg count\n"^
                                    "shl rbx , 3 ; rbx = rbx * 8\n"^
                                    "add rsp , rbx; pop args\n"^
                                    ".after_applic_"^labelnum^":\n"
                            | arg :: rest -> (genAssembly constTbl fvTable nestCount arg)^
                                              "push rax\n"^
                                              (applicExpander rest) in
                              (applicExpander args_rev)
                              

| ScmDef'(VarFree(v),value) ->
      let fvarLabel = getFvarLabel v (fvTable) in
      (genAssembly constTbl fvTable nestCount value) ^
      "mov qword[fvar_tbl + 8*"^fvarLabel^"], rax \n" ^
      "mov rax, SOB_VOID_ADDRESS \n"

| _ -> raise X_not_yet_implemented;;
  let generate consts fvars e = genAssembly consts fvars 0 e;;
end;;

