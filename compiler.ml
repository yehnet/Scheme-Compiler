#use "code-gen.ml";;
#use "prims.ml";;


exception Debug of ((string * int) list);;
(* 
   Auxiliary function to load the contents of a file into a string in memory.
   Note: exceptions are not handled here, and are expected to be handled 
   by the caller. We already took care of this in main code block below.
 *)
let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let get_first_element tuple = 
  match tuple with 
  | (a,b) -> a
  (* | _ -> raise X_this_should_not_happen;; *)
  

let rec exists_in_fvars_table elm fvars_table =
  match fvars_table with
  | [] -> false
  | car::cdr -> if elm=(get_first_element car) then true 
                                             else (exists_in_fvars_table elm cdr)

let add_to_fvars_table elm fvars_table = 
if (exists_in_fvars_table elm fvars_table) then fvars_table 
else
let last_index = (List.length fvars_table) - 1 in
fvars_table @ [(elm, last_index + 1)]


let populate_fvars_tbl fvars_tbl primitive_names_to_labels = 
  List.fold_left (fun a next -> 
    (add_to_fvars_table (get_first_element next) a)) fvars_tbl primitive_names_to_labels;;

(* This procedure creates the assembly code to set up the runtime environment for the compiled
   Scheme code. *)
let make_prologue consts_tbl fvars_tbl =
  (* The table defines a mapping from the names of primitive procedures in scheme to their labels in 
     the assembly implementation. *)
  let primitive_names_to_labels =
  [
    (* Type queries  *)
    "boolean?", "boolean?"; "flonum?", "flonum?"; "rational?", "rational?";
    "pair?", "pair?"; "null?", "null?"; "char?", "char?"; "string?", "string?";
    "procedure?", "procedure?"; "symbol?", "symbol?";
    (* String procedures *)
    "string-length", "string_length"; "string-ref", "string_ref"; "string-set!", "string_set";
    "make-string", "make_string"; "symbol->string", "symbol_to_string";
    (* Type conversions *)
    "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "exact->inexact", "exact_to_inexact";
    (* Identity test *)
    "eq?", "eq?";
    (* Arithmetic ops *)
    "+", "add"; "*", "mul"; "/", "div"; "=", "eq"; "<", "lt";
    (* Additional rational numebr ops *)
    "numerator", "numerator"; "denominator", "denominator"; "gcd", "gcd";
    (* you can add yours here *)
    "car","my_car";"cdr","my_cdr";"cons","my_cons" ; "set-car!","my_set_car"; "set-cdr!","my_set_cdr" ; "apply","my_apply"
  ] in
  (* POPULATE FVARS TABLE WITH PRIMS *)
  let fvars_tbl = populate_fvars_tbl fvars_tbl primitive_names_to_labels in
  (* let debug = raise (Debug fvars_tbl) in *)
  
  let make_primitive_closure (prim, label) =
    
    (* This implementation assumes fvars are addressed by an offset from the label `fvar_tbl`.
       If you use a different addressing scheme (e.g., a label for each fvar), change the 
       addressing here to match. *)
    "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")\n" ^
      "mov [fvar_tbl+8*" ^ (string_of_int (List.assoc prim fvars_tbl)) ^ "], rax" 
     in
  let constant_bytes (c, (a, s)) =
    (* Adapt the deconstruction here to your constants data generation scheme.
       This implementation assumes the bytes representing the constants are pre-computed in
       the code-generator and stored in the last column of a three-column constants-table structure *)
    s in
    
";;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

%macro MAKE_LITERAL_STRING 1+
  db T_STRING
  dq (%%end_str - %%str)
  %%str:
    db %1
  %%end_str:
%endmacro

%macro MAKE_LITERAL_VECTOR 0-*
  db T_VECTOR
  dq %0
  %rep %0
    dq %1
  %rotate 1
  %endrep
%endmacro

%macro MAKE_LITERAL_SYMBOL 1
  db T_SYMBOL
  dq %1
%endmacro



%macro SHIFT_FRAME 2
	mov rcx, %1
	%%body:
  	mov rbx, qword[rsp+8*(rcx - 1)]
    mov rdx, rcx
    sub rdx, 1
    add rdx, %2
  	mov qword[rsp+8*(rdx)], rbx
	loop %%body
%endmacro
%macro SHIFT_FRAME_DOWN 0
  push 0x0 ;;dummy
  mov rcx, qword[rbp+8*3] ;;rcx = argnum
  add rcx, 4 ;;rcx = frame_size
  mov rbx, rcx
  %%body:
    mov rdx, rbx
    sub rdx, rcx
    mov r11, qword[rbp+8*(1+rdx)]
    mov qword[rbp+8*(rdx)], r11
  loop %%body
  ;sub rsp, 8  ;;; ??SUSPICOIOUS ;;;
  sub rbp, 8
%endmacro
%define FVAR(i) [fvar_tbl + i * WORD_SIZE]
%macro COPY_ENV 2
	MALLOC rax, %1
	mov rbx, qword[rbp+8*2]
	mov r10, rax
	mov rcx, %2
	%%body:
		cmp rcx, 0
		je %%end
		add rax, 8
		mov rdx, qword[rbx]
		mov qword[rax], rdx
		add rbx, 8
		dec rcx
		jmp %%body
	%%end:
%endmacro

not_closure_error_msg: db \"Error: a non-closure argument was given for application\", 0

%define SOB_UNDEFINED T_UNDEFINED
%define SOB_NIL T_NIL
%define SOB_VOID T_VOID
%define SOB_FALSE word T_BOOL
%define SOB_TRUE word (1 << TYPE_SIZE | T_BOOL)

section .bss
;;; This pointer is used to manage allocations on our heap.
malloc_pointer:
    resq 1

;;; here we REServe enough Quad-words (64-bit \"cells\") for the free variables
;;; each free variable has 8 bytes reserved for a 64-bit pointer to its value
fvar_tbl:
    resq " ^ string_of_int (List.length fvars_tbl) ^ "

section .data
const_tbl:
" ^ (String.concat "\n" (List.map constant_bytes consts_tbl)) ^ 
"

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS const_tbl+" ^  (string_of_int (fst (List.assoc ScmVoid consts_tbl))) ^ "
%define SOB_NIL_ADDRESS const_tbl+" ^   (string_of_int (fst (List.assoc (ScmNil) consts_tbl))) ^ "
%define SOB_FALSE_ADDRESS const_tbl+" ^ (string_of_int (fst (List.assoc (ScmBoolean false) consts_tbl))) ^ "
%define SOB_TRUE_ADDRESS const_tbl+" ^  (string_of_int (fst (List.assoc (ScmBoolean true) consts_tbl))) ^ 

"

global main
section .text
main:
    ;; set up the heap
    mov rdi, GB(2)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0                ; argument count
    push SOB_NIL_ADDRESS  ; lexical environment address
    push T_UNDEFINED      ; return address
    push rbp                    
    mov rbp, rsp                ; anchor the dummy frame

    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we simulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ "

user_code_fragment:
;;; The code you compiled will be added here.
;;; It will be executed immediately after the closures for 
;;; the primitive procedures are set up.\n";;

let clean_exit =
  ";;; Clean up the dummy frame, set the exit status to 0 (\"success\"), 
   ;;; and return from main
   pop rbp
   add rsp, 3*8
   mov rax, 0

   ret"^
  
"\nmy_car:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
SKIP_TYPE_TAG rax, rsi
jmp .return
.wrong_type:
mov rax, SOB_FALSE_ADDRESS
.return:
leave
ret

my_cdr:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
mov cl, byte[rsi]
cmp cl, T_PAIR
;  jne .wrong_type
mov rax, qword [rsi+WORD_SIZE +TYPE_SIZE]
jmp .return
.wrong_type:
mov rax, SOB_FALSE_ADDRESS
.return:
leave
ret

my_set_car:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
mov rax, PVAR(1)
mov qword[rsi+TYPE_SIZE], rax
mov rax, SOB_VOID_ADDRESS
.return:
leave
ret

my_set_cdr:
push rbp
mov rbp, rsp
mov rsi, PVAR(0)
mov rax, PVAR(1)
mov qword[rsi+TYPE_SIZE+WORD_SIZE], rax
mov rax, SOB_VOID_ADDRESS
.return:
leave
ret

my_cons:
push rbp
mov rbp, rsp
mov rbx, PVAR(0)
mov rcx, PVAR(1)
MAKE_PAIR(rax, rbx, rcx )
jmp .return
.wrong_argcount:
mov rax, SOB_FALSE_ADDRESS
.return:
leave
ret

my_apply:
push rbp
mov r15, rbp ;;backup rbp
mov rbp, rsp
mov rcx, qword[rbp+8*3] ;;rcx=argnum
mov r10, qword[rbp+8*4] ;; r10 = arg0
mov r10, qword[r10+TYPE_SIZE] ;; r10 = arg0_env
mov r13, qword[rbp+8*4] ;;r13 = arg0
mov r13, qword[r13+TYPE_SIZE+WORD_SIZE] ;; r13 = arg0_Lcode
mov r11, qword[rbp+8*1] ;; r11 = ret address
mov r12, qword[rbp+8*3] ;; r12 = argnum_backup
mov r8, qword[rbp+8*3]
mov rsi, qword[rbp+8*(4+ r8 - 1)] ;;rsi = last arg = proper list
sub r8, 2 ;; r8=num of regular args= total_args - proc - list
sub rcx, 2
mov rax, rcx
cmp rcx, 0
je .push_list
.push_args:
mov r8, rax
sub r8, rcx
push qword[rbp+8*(4+1+r8)]
loop .push_args
mov r8, qword[rbp+8*3]
mov rsi, qword[rbp+8*(4+ r8 - 1)] ;;rsi = last arg = proper list
sub r8, 2 ;; r8=num of regular args= total_args - proc - list
.push_list:
cmp rsi, SOB_NIL_ADDRESS
je .after_push_list
SKIP_TYPE_TAG rax, rsi
inc r8
push rax
mov rsi, qword [rsi+WORD_SIZE +TYPE_SIZE] ;;rsi = (cdr rsi)
jmp .push_list
.after_push_list:
mov rcx, r8 ;; rcx = r8 = argnum
mov rbx, rsp
cmp rcx, 0
je .push_argnum_env_ret
.reverse:
push qword[rbx]
add rbx, 8
loop .reverse
SHIFT_FRAME r8, r8
mov r9, r8
imul r9, 8
add rsp, r9
.push_argnum_env_ret:
push r8 ;; push argnum
push r10 ;; push arg0_env
push r11 ;; push ret_addr
mov rax, 4 ;; rax = count(rbp+ret+env+argnum)
add rax, r12 ;; rax = rax + original_argnum = old frame size
mov rbx, 3
add rbx, r8 ;; rbx = rbx + argnum = new_frame_size
SHIFT_FRAME rbx, rax
;; calc frame sizes AGAIN because SHIFT_FRAME corrupts rbx,rax
mov rax, 4 ;; rax = count(rbp+ret+env+argnum)
add rax, r12 ;; rax = rax + original_argnum = old frame size
mov rbx, 3
add rbx, r8 ;; rbx = rbx + argnum = new_frame_size
mov rcx, rbx
sub rcx, rax ;rcx = new - old
sub rbx, rcx ;; rbx = new - (old-new)
imul rbx, 8
add rsp, rbx
mov rbp, r15
.finish_apply:
jmp r13 ;; call function
add rsp , 8*1 ; pop env
pop rbx ; pop arg count
shl rbx , 3
add rsp , rbx; pop args
leave
ret";;

exception X_missing_input_file;;

(* 
   This is the bit that makes stuff happen. It will try to read a filename from the command line arguments
   and compile that file, along with the contents of stdlib.scm.
   The result is printed to stduot. This implementation assumes the compiler user redirects the output to a 
   file (i.e. "ocaml compiler.ml some_file.scm > output.s").
   This assumption is already handled correctly in the provided makefile.
 *)
try
  (* Compile a string of scheme code to a collection of analyzed ASTs *)
  let string_to_asts s = List.map Semantic_Analysis.run_semantics
                           (List.map Tag_Parser.tag_parse_expression
                              ((PC.star Reader.nt_sexpr) s 0).found) in

  (* get the filename to compile from the command line args *)
  let infile = Sys.argv.(1) in  

  (* load the input file and stdlib *)
  let code =  (file_to_string "stdlib.scm") ^ (file_to_string infile) in

  (* generate asts for all the code *)
  let asts = string_to_asts code in
  
  (* generate the constants table *)
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  (* let debug = raise (Code_Gen.Miro ((List.nth asts ((List.length asts)-1)), (string_of_int (List.length asts)))) in *)
  (* generate the fvars table *)
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in  

  (* Generate assembly code for each ast and merge them all into a single string *)
  let generate = Code_Gen.generate consts_tbl fvars_tbl in 
  let code_fragment = String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n\tcall write_sob_if_not_void")
                           asts) in

  (* merge everything into a single large string and print it out *)
  print_string ((make_prologue consts_tbl fvars_tbl)  ^ 
                  code_fragment ^ clean_exit ^
                    "\n" ^ Prims.procs)

(* raise an exception if the input file isn't found *)
with Invalid_argument(x) -> raise X_missing_input_file;;