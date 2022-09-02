(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

(* open Pc.PC;; *)

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)

module Reader : READER  = struct 
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

(* and nt_paired_comment str = 
let left_curly_brace = char '{' in
let rest = (star (diff nt_any (char '}'))) in
let paired_comment_parser = caten left_curly_brace (caten rest (char '}')) in
let packed_comment_parser = pack paired_comment_parser (fun _ ->()) in
packed_comment_parser str *)



and nt_sexpr_comment str= 
let tok_BeginOfSComment = word "#;" in 
  pack (caten tok_BeginOfSComment (nt_sexpr)) 
  (fun (_)-> ()) str

and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str

and nt_line_comment str = 
  let comment_start = (char ';') in
  let eof_parser = unitify nt_end_of_input in
  let eol_parser = unitify (word "\n") in
  let comment_content = star (diff nt_any (disj eol_parser eof_parser)) in
  let comment_parser = (caten comment_start comment_content) in 
  pack comment_parser (fun _ ->()) str

and nt_paired_comment str = 
  let forbidden = disj_list [(unitify nt_char);
                             (unitify nt_string);
                             (unitify nt_comment)] in
  let forbidden' = disj_list [forbidden; unitify (char '{'); unitify (char '}')] in
  let inside = diff nt_any forbidden' in
  let inside = disj (unitify inside) forbidden in
  let inside = star inside in
  let nt = caten (char '{') (caten inside (char '}')) in
  unitify nt str
  
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1

and nt_digit_0_to_9 str = pack (const (fun ch -> '0' <= ch && ch <= '9'))
                                (let ascii_0 = int_of_char '0' in 
                                (fun ch-> (int_of_char ch) - ascii_0)) str
and nt_natural str = let rec nt str = pack (caten nt_digit_0_to_9 (disj nt nt_epsilon))
                                           (function (a, s)-> a::s) str in
                                           pack nt (fun s-> List.fold_left 
                                                              (fun a b -> 10 * a + b)
                                                              0
                                                              s) str
and nt_int str = 
let sign = maybe (disj (char '+') (char '-')) in 
let int_parser = caten sign nt_natural in
pack int_parser (fun(s, n)-> if s=Some('-') then n*(-1) else n) str

and nt_frac str = pack (caten nt_int (caten (char '/') (nt_natural)))
                        (fun(a,(div,b))-> ScmRational(a,b)) str
and nt_integer_part str = nt_natural str
and nt_mantissa str = nt_natural str

and exponent_token str = pack (disj_list [(word "e");(word "E");(word "*10^");(word "*10**")])
                              (fun _ -> 'e') str
and nt_exponent str = pack (caten exponent_token nt_int)
                           (fun(c,n)-> "e"^(string_of_int n)) str

(* and float_a str = pack (caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent)))) str
                        *)

(* ((((Float))))) *)
and nt_float str = 
let maybe_exponent = pack (maybe nt_exponent)
                          (fun(e)->match e with
                                  | Some(x) -> x
                                  | None -> "") in

let maybe_mantissa = pack (maybe nt_mantissa)
                    (fun(e)->match e with
                            | Some(x) -> (string_of_int x)
                            | None -> "") in

let floatA = pack (caten nt_integer_part (caten (char '.') (caten (maybe_mantissa) (maybe_exponent))))
                  (fun(it,(d,(mnt,exp)))-> (float_of_string ((string_of_int it)^"."^mnt^exp))) in  
let floatB = pack (caten (char '.') (caten (nt_mantissa) (maybe_exponent)))
                  (fun(d,(mnt,ex))->(float_of_string ("."^((string_of_int mnt )^ ex)))) in
let floatC = pack (caten nt_natural nt_exponent)
                  (fun(n,st)->(float_of_string ((string_of_int n)^st))) in
pack (disj_list [floatA;floatB;floatC])
     (fun(f)-> ScmReal(f)) str
(* let floatA = caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent))) in  
let floatB = (caten (char '.') (caten nt_mantissa (maybe nt_exponent))) in
let floatC = caten nt_natural nt_exponent in
(disj floatA (disj floatB floatC)) *)

and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str = pack (disj (word_ci "#t") (word_ci "#f"))
                          (fun(pr)->if pr=['#';'t'] || pr=['#';'T'] then ScmBoolean(true) else ScmBoolean(false)) str
and nt_char_simple str = 
let range_of_chars = (range '!' '~') in
(* let nt1 = diff nt_any nt_skip_star in *)
pack (not_followed_by range_of_chars range_of_chars)
                          (fun(c)->ScmChar(c)) str
                          
and make_named_char char_name ch = pack (word char_name) (fun(s)-> ScmChar(ch))
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t');
               (make_named_char "nul" '\000')] in
  nt1 str
and nt_char_hex str = disj_list [(range '0' '9');(range 'a' 'f');(range 'A' 'F')] str

and char_hex str = 
let x = char 'x' in
let hex = (plus nt_char_hex) in
pack (caten x hex)
    (fun(a,b)-> match b with
              | [] -> raise X_no_match
              | lst -> ScmChar(char_of_int (int_of_string ("0x"^(list_to_string lst))))) str

and char_prefix str = (word "#\\") str
and nt_char str = pack (caten char_prefix (disj_list [nt_char_named;char_hex;nt_char_simple]))
                      (fun(a,b) -> b) str
and nt_symbol_char str =
  let digit_token = range '0' '9' in
  let lowercase_token = range 'a' 'z' in
  let uppercase_token = range 'A' 'Z' in
  let other_chars = disj_list[char ('!');char '$';char '^';char '*';char '-';char '_';char '=';char '+';char '<';char '>';char '?';char '/';char ':'] in
  disj_list [digit_token;lowercase_token;uppercase_token;other_chars] str

and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str

and nt_string_char str = 
  let string_literal_char = pack (diff (nt_any) (disj_list [(char '\\');(char '~');(char '"')]))
  (fun(s)->String.make 1 s) in
  let backslash = char '\\' in 
  let meta = (disj_list [char '\"'; char 't'; char 'f'; char 'n'; char 'r';char '\\']) in 
  let string_meta_char = pack (caten backslash meta)
                              (fun(a,b)->match b with
                                        | 't' -> "\009"
                                        | 'n' -> "\010"
                                        | 'r' -> "\013"
                                        | 'f' -> "\012"
                                        | _ -> "\\"^(String.make 1 b)) in
  let tilde = pack (word "~~") (fun(_)-> "~") in
  let string_meta_char = disj string_meta_char tilde in
  let string_hex_char =  pack (caten (word "\\x") (plus nt_char_hex))
                              (fun(a,b)-> list_to_string (a@b)) in
                        disj_list [string_hex_char;string_meta_char;string_literal_char] str

and list_of_strings_to_string str_list = (List.fold_left (^) "" str_list)


and nt_string_only str = 
  let str_star = plus (nt_string_char) in
  pack  str_star
       (fun(a)-> ScmString(list_of_strings_to_string a)) str

and nt_string_interpolated str = 
  let tok_tilde = (char '~') in
  let beg_interpolated =  (char '{') in 
  let end_interpolated = char '}' in
  pack (caten tok_tilde (caten beg_interpolated ( caten nt_sexpr end_interpolated)))
                                (fun (_,(_,(exp,_))) -> ScmPair( ScmSymbol("format") , ScmPair( ScmString ("~a"), ScmPair(exp,ScmNil)))) str

and nt_string str =
    let double_quote = (char '\"') in
    let str_star = star (disj nt_string_interpolated nt_string_only ) in
          pack (caten double_quote (caten str_star double_quote))
           (fun (_,(elems,_)) -> match elems with
                  | [] -> ScmString ""
                  | hd::[] -> hd
                  | hd::tl -> list_to_proper_list([ScmSymbol "string-append"]@elems)) str

and list_to_proper_list = function
                        | [] -> ScmNil
                        | hd::tl -> ScmPair(hd, list_to_proper_list tl)
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str

and pairElements lst = match lst with
  | [] -> ScmNil
  | x::y -> ScmPair(x, pairElements y)

and pairTwoElement lst el = match lst with
  | [] -> el
  | x::y -> ScmPair(x, pairTwoElement y el)
(* properList | improperList *)
and nt_list str = 
  let properList = pack (caten (char '(') (caten nt_skip_star (caten (star nt_sexpr) (char ')'))))
    (fun (_,(_,(s,_))) -> pairElements s) in
  let carIm = plus nt_sexpr  in
  let improperList = pack (caten (char '(') (caten nt_skip_star (caten carIm (caten (char '.') (caten nt_sexpr (char ')' ))))))
      (fun(_,(_ ,(s,(_,(l,_))))) -> pairTwoElement s l) in
                      (disj properList improperList) str
  
    (* quoted forms *)
and nt_quoted_forms str = 
    let quoted = pack (caten (char '\x27') nt_sexpr)
                  (fun(_,s) -> ScmPair(ScmSymbol("quote"),ScmPair(s,ScmNil))) in
    let quasiQuoted = pack (caten (char '`') nt_sexpr)
                  (fun (_,s) -> ScmPair(ScmSymbol("quasiquote"), ScmPair(s,ScmNil))) in
    let unquoted = pack (caten (char ',') nt_sexpr)
                  (fun (_,s) -> ScmPair(ScmSymbol("unquote"), ScmPair(s,ScmNil))) in
    let unquoteandSpliced = pack (caten (word ",@") nt_sexpr)
                  (fun (_,s) -> ScmPair(ScmSymbol("unquote-splicing"), ScmPair(s, ScmNil))) in
    disj_list [quoted;quasiQuoted;unquoted;unquoteandSpliced] str
    

and nt_sexpr str = 
  (* let nt1 = nt_boolean in *)
  let nt1 = disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
