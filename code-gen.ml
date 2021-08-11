(* pc.ml
 * A parsing-combinators package for ocaml
 *
 * Prorammer: Mayer Goldberg, 2018
 *)

(* general list-processing procedures *)

let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)

(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
 open PC;;
 exception X_not_yet_implemented;;
 exception X_this_should_not_happen;;
   
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
 let rec sexpr_eq s1 s2 =
   match s1, s2 with
   | Bool(b1), Bool(b2) -> b1 = b2
   | Nil, Nil -> true
   | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
   | Number(Int n1), Number(Int n2) -> n1 = n2
   | Char(c1), Char(c2) -> c1 = c2
   | String(s1), String(s2) -> s1 = s2
   | Symbol(s1), Symbol(s2) -> s1 = s2
   | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
   | Vector(l1), Vector(l2) ->if(List.length l1 !=List.length l2)then false else ( List.for_all2 sexpr_eq l1 l2)
   | _ -> false;;
   
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;
 
 
 
 let nt_Digit = one_of "0123456789";;
 (******************************** Boolean parser**********************************************************************)
 let nt_BooleanParser s = 
   let ((a,b),c) = (not_followed_by (caten (char '#') (disj (char_ci 't') (char_ci 'f'))) nt_Digit)  s in
   match b with 
   | 't'-> (Bool true,c)
   | 'T'-> (Bool true,c)
   | 'f'-> (Bool false,c)
   | 'F'-> (Bool false,c)
   | _-> raise X_this_should_not_happen;;
 
 
 (******************************** Char parser**********************************************************************)
 let nt_CharPrefixParser =caten ( char '#') (char '\\') ;;
 
 let nt_VisibleSimpleChar s =let (a,s)=nt_any s in (a,s);;
 
 let nt_newline=(word_ci "newline");;
 let nt_nul=(word_ci "nul");;
 let nt_page=(word_ci "page");;
 let nt_return=(word_ci "return");;
 let nt_space=(word_ci "space");;
 let nt_tab=(word_ci "tab");;
 
 let nt_NamedChar s = 
   let (c,s) = (disj_list [nt_newline;nt_return;nt_tab;nt_space;nt_nul;nt_page]) s in
   match (list_to_string (List.map lowercase_ascii c)) with
   | "newline"-> (Char.chr 10,s)
   | "nul"-> (Char.chr 0,s)
   | "return"-> (Char.chr 13,s)
   | "tab"-> (Char.chr 9,s)
   | "page"-> (Char.chr 12,s)
   | "space"-> (Char.chr 32,s)
   | _->raise X_this_should_not_happen;;
 
 let nt_HexCharDigit = one_of_ci "0123456789abcdefABCDEF";;
 let nt_HexChar s =
   let((x,x1),s) =(caten(char_ci 'x')(plus nt_HexCharDigit)) s in
     (Char.chr(int_of_string ("0x"^(list_to_string x1))),s);;
   
 let nt_CharParser s =
   let (((solamet, slash),c),s) = caten nt_CharPrefixParser (disj_list [nt_NamedChar; nt_HexChar ;nt_VisibleSimpleChar])  s in (Char c,s);;
 
 (********************************************* Number Parser***************************************************)
 
 let nt_HexDigit=one_of "0123456789abcdefABCDEF";;
 let nt_MinusOrPlus s= (disj (char '+') (char '-')) s  ;;
 let nt_NaturalNumber=plus nt_Digit;;
 let nt_HexNumber = plus nt_HexDigit;;
  
 let nt_HexIntegerParser s= 
    pack (caten (char '#') (caten (char_ci 'x')(caten (maybe nt_MinusOrPlus) nt_HexNumber))) 
    (fun(solamet,(x,(sign,n)))->
     match sign with
     | Some('+') -> Int(int_of_string ("0x"^(list_to_string(n))))
     | Some('-') -> Int(int_of_string ("0x"^(list_to_string(n))) * -1)
     |_->Int(int_of_string ("0x"^list_to_string n))) s;; 
     
   
 let nt_IntegerParser s = pack (caten (maybe nt_MinusOrPlus) nt_NaturalNumber) 
   (fun (sign,n)-> 
   match sign with
     | Some('+') -> Int(int_of_string (list_to_string n))
     | Some('-') -> Int((int_of_string (list_to_string n)) * -1)
     |_->Int(int_of_string(list_to_string n))) s;;
 
 
 let nt_FloatParser s = pack (caten (maybe nt_MinusOrPlus) (caten nt_NaturalNumber (caten (char '.') nt_NaturalNumber)))
   (fun (sign,(n1,(dot,n2)))->
     match sign with
     |Some('+') -> Float(float_of_string (list_to_string(n1@dot::n2)))
     |Some('-') -> Float((float_of_string (list_to_string(n1@dot::n2)) *. -1.0))
     |_->Float(float_of_string (list_to_string(n1@dot::n2)))) s;;
 
 let nt_HexFloatParser s = pack ( caten (char '#') (caten (char_ci 'x') (caten (maybe nt_MinusOrPlus) (caten nt_HexNumber (caten (char '.') nt_HexNumber)))))
   (fun (solmet,(x,(sign,(n1,(dot,n2)))))->
   match sign with
   |Some('+') -> Float(float_of_string(("0x" ^ list_to_string n1) ^ "." ^(list_to_string n2)))
   |Some('-') -> Float((float_of_string(("0x" ^ list_to_string n1) ^ "." ^ (list_to_string n2))) *. -1.0)
   |_ -> Float(float_of_string(("0x" ^ list_to_string n1) ^ "." ^(list_to_string n2)))) s;;
 
 
 
 let nt_ExIntegerParser s = let (n,s)=nt_IntegerParser s in 
   match n with 
   |Int(x)->(float_of_int(x),s)
   |_->raise X_this_should_not_happen;;
 
 let nt_ExFloatParser s = let (n,s)=nt_FloatParser s in 
 match n with 
   |Float(x)->(x,s)
   |_->raise X_this_should_not_happen;;
   
 let nt_Exponent s = pack ( caten (disj_list[nt_ExFloatParser ;nt_ExIntegerParser]) (caten (char_ci 'e') nt_ExIntegerParser))
   (fun (n1,(e,n2))->Float(float_of_string(list_to_string((string_to_list(string_of_float n1))@'e'::(string_to_list(string_of_int (int_of_float n2))))))) s;;
 
 
         
 let nt_sym =disj (range_ci 'a' 'z') (one_of  "/0123456789!$^*-_=+<>?/:");;
 let nt_NumberParser s = 
   let (n,s) = (not_followed_by (disj_list [nt_Exponent;nt_HexFloatParser;nt_FloatParser;nt_IntegerParser;nt_HexIntegerParser]) nt_sym ) s in (Number(n),s);;
 
 (********************************************* String Parser***************************************************)
 let nt_Allchars= disj_list [(range_ci (Char.chr 0) (Char.chr 33)); (range_ci (Char.chr 35) (Char.chr 91));(range_ci (Char.chr 93) (Char.chr 127))];;
 let nt_NonQuote = disj_list [range (Char.chr 0)(Char.chr 33); range (Char.chr 35) (Char.chr 127)];;
 
 let nt_newline s = let(_,s) = (word_ci "\\n") s in ('\n',s);;
 let nt_page s = let(_,s) = (word_ci "\\f") s in ('\012',s);;
 let nt_return s = let(_,s) = (word_ci "\\r") s in ('\r',s);;
 let nt_tab s = let(_,s) = (word_ci "\\t") s in ('\t',s);;
 let nt_slash s = let(_,s) = (word_ci "\\\\") s in ('\\',s);;
 let nt_quote s = let(_,s) = (word_ci "\\\"") s in ('\"',s);;
 
 let nt_StringMetaCharParser s =  disj_list[nt_newline;nt_page;nt_return;nt_tab;nt_slash;nt_quote] s ;;
 let nt_StringLiteralCharParser s = let (c,s)= nt_Allchars s in (c,s);;
 
 let nt_StringHexCharParser s = pack (caten (char '\\') (caten (char_ci 'x') (caten (plus nt_HexDigit) (char ';'))))
   (fun (slash,(x,(str,semi)))->Char.chr(int_of_string ("0x"^(list_to_string str)))) s;;
 
 let nt_StringChar s = (disj_list[nt_StringHexCharParser; nt_StringMetaCharParser; nt_StringLiteralCharParser]) s;;
 
 let nt_StringParser s = pack (caten (char '\"') (caten (star(nt_StringChar)) (char '\"')))
   (fun(quote1,(str,quote2))->String(list_to_string str)) s;;
 
 
 (********************************************* symbol parser***************************************************)
 
 let nt_SymbolChar s = 
   let (ch1,s) = nt_sym s in
     let ch2 = lowercase_ascii ch1 in (ch2, s);;
 
 let nt_SymbolParser s = 
   let (sym,s) = plus nt_SymbolChar  s in
     (Symbol(list_to_string sym),s);;
 
 
 (******************************************* whitespaces ************************************)
 
 let nt_WhitespacesParser s = let (spaces, s1)= (star nt_whitespace)  s in
   (list_to_string s1);;
 
 (******************************************** Comment****************************************)
 let nt_EndOfLine s = let (eol,s) = (char '\n') s in ([eol],s);;
 let nt_EndOfLine_Or_EndOfInput= disj nt_end_of_input nt_EndOfLine;;
 
 let nt_NonSemicolon= disj_list [range (Char.chr 0)(Char.chr 58); range (Char.chr 60) (Char.chr 127)];;
 
 let nt_NonNL = disj_list [range (Char.chr 0)(Char.chr 9); range (Char.chr 11) (Char.chr 127)];;
 
 let nt_CommentParser s = pack (caten (char ';') (caten (star nt_NonNL) (nt_EndOfLine_Or_EndOfInput)))
   (fun(coma,(comment,eol))->' ') s;;
 
 
 (*********************************************pair parser *****************************************)
 let nt_LeftParent s = (disj(char '(')(char '[')) s;;
 let nt_RightParent s = (disj(char ')')(char ']')) s;;
 let nt_3dots s = let(dots,s) = (word "...") s in (' ',s);;
 let nt_Dot s = (char '.') s;;
 let nt_solamet s = (char '#') s;;
 let make_enclosed l exp r = let exp = caten(caten l exp) r in pack exp (fun((l,exp),r) ->exp);;
 let nt_Nonrightparent = disj_list [range (Char.chr 0)(Char.chr 40); range (Char.chr 42) (Char.chr 127)];;
 
 
 let rec nt_Sexpr s  =
   let (spaces,s) = star (disj nt_whitespace nt_CommentParser) s in 
   (disj_list[nt_BooleanParser; nt_CharParser; nt_NumberParser; nt_StringParser;nt_SymbolParser;nt_SexpList;nt_SexpDottedList;nt_VectorParser;nt_SexpListBracket;nt_SexpDottedListBracket;nt_VectorParserBracket;nt_Quoted;nt_QQouted;nt_Unqouted;nt_UnquotedSpliced;nt_SexprComment; nt_Ellipsis]) s and
 
 nt_SexpList s=
   (pack ((make_enclosed (char '(') (star nt_Sexpr) (caten (star(disj nt_CommentParser nt_whitespace))  (char ')') )))
   (fun (exp)->((List.fold_right (fun e acc -> Pair(e,acc)) exp Nil))) s)  and
   
 nt_SexpDottedList s= (pack (caten (char '(') (caten (plus nt_Sexpr) (caten (make_enclosed (star (disj nt_CommentParser nt_whitespace)) (char '.') (star (disj nt_CommentParser nt_whitespace)))(caten nt_Sexpr (caten (star (disj nt_CommentParser nt_whitespace))  (char ')'))  )))) 
   (fun (lparen,(exp1,(dot,(exp,(spaces,quote)))))->(List.fold_right (fun e acc -> Pair(e,acc)) exp1 exp)) s)  and
 
 nt_VectorParser s= (pack (caten (char '#') (caten (char '(') (caten (star nt_Sexpr) (caten (star (disj nt_CommentParser nt_whitespace)) (char ')')))))
   (fun(solmet,(lquote,(sexplist,(spaces,rquote))))->Vector sexplist) s) and
 
 nt_SexpListBracket s=
   (pack ((make_enclosed (char '[') (star nt_Sexpr) (caten (star(disj nt_CommentParser nt_whitespace))  (char ']') )))
   (fun (exp)->((List.fold_right (fun e acc -> Pair(e,acc)) exp Nil))) s)  and 
 
 nt_SexpDottedListBracket s=
   (pack (caten (char '[') (caten (plus nt_Sexpr) (caten (make_enclosed (star (disj nt_CommentParser nt_whitespace)) (char '.') (star (disj nt_CommentParser nt_whitespace)))(caten nt_Sexpr (caten (star (disj nt_CommentParser nt_whitespace))  (char ']'))  )))) 
   (fun (lparen,(exp1,(dot,(exp,(spaces,quote)))))->(List.fold_right (fun e acc -> Pair(e,acc)) exp1 exp)) s)   and
 
 nt_VectorParserBracket s=
   (pack (caten (char '#') (caten (char '[') (caten (star nt_Sexpr) (caten (star (disj nt_CommentParser nt_whitespace)) (char ']')))))
   (fun(solmet,(lquote,(sexplist,(spaces,rquote))))->Vector sexplist) s) and
 
 nt_Quoted s = (pack (caten (word "'") nt_Sexpr)
   (fun(quote,exp)->Pair(Symbol("quote"),Pair(exp,Nil))) s) and
 
 nt_QQouted s= (pack (caten (word "`") nt_Sexpr)
   (fun(quote,exp)->Pair(Symbol("quasiquote"),Pair(exp,Nil))) s) and
 
 nt_UnquotedSpliced s= (pack (caten (char ',') (caten (char '@') nt_Sexpr)) 
   (fun(a,(b,exp))->Pair(Symbol("unquote-splicing"),Pair(exp,Nil))) s) and
 
 nt_Unqouted s=(pack (caten (word ",") nt_Sexpr)
   (fun(quote,exp)->Pair(Symbol("unquote"),Pair(exp,Nil))) s) and
 
 nt_SexprComment s = (pack (caten (char '#') (caten (char ';') (caten nt_Sexpr nt_Sexpr)))
   (fun(solamet,(semicolon,(exptoremove,exp)))->exp) s) and
 
 nt_DotsSexpList s= (pack (make_enclosed nt_LeftParent (star nt_HelperEllipsis) (caten (star (disj nt_CommentParser nt_whitespace))  (maybe nt_RightParent) )) 
   (fun(exp)->(List.fold_right (fun e acc -> Pair(e,acc)) exp Nil)) s) and 
 
 nt_DotVectorParser s= (pack (caten (char '#') (caten nt_LeftParent (caten (star nt_HelperEllipsis) (caten (star (disj nt_CommentParser nt_whitespace)) (maybe nt_RightParent)))))
   (fun(solmet,(lquote,(sexplist,(spaces,rquote))))->Vector sexplist)  s) and
 
 nt_DotSexpDottedList s= ( pack (caten nt_LeftParent (caten (plus nt_Sexpr) (caten (make_enclosed (star (disj nt_CommentParser nt_whitespace)) (char '.') (star (disj nt_CommentParser nt_whitespace)))   (caten nt_HelperEllipsis (caten (star (disj nt_CommentParser nt_whitespace))  (maybe nt_RightParent) )) )))
  (fun(lparen,(exp1,(dot,(exp,(spaces,quote)))))->(List.fold_right (fun e acc -> Pair(e,acc)) exp1 exp)) s)and
 
 nt_Ellipsis s =
 (pack (make_enclosed (star (disj nt_CommentParser nt_whitespace))
   (disj_list[ nt_DotSexpDottedList;nt_DotsSexpList; nt_DotVectorParser]) (caten(star (disj nt_CommentParser nt_whitespace)) nt_3dots)) (fun(exp)->exp) s) and
 
 nt_HelperEllipsis s = (pack (caten (star (disj nt_CommentParser nt_whitespace)) (disj_list[ diff nt_Sexpr nt_Ellipsis; nt_DotSexpDottedList; nt_DotsSexpList; nt_DotVectorParser]))
   (fun(spaces,exp)->exp) s);;
 
 let nt_Ignore3Dots s = (pack (caten (star (disj nt_CommentParser nt_whitespace)) (word "...")  ) (fun(spaces,dots)->(dots,s))  s)
 
 let nt_remove3dots s=
   let(a,b)= maybe(nt_Ignore3Dots) s in
     nt_Sexpr b;;
 
 let read_sexpr string = let (exp,s) = (star nt_remove3dots) (string_to_list string) in 
 if (List.length exp > 1) then raise X_no_match 
 else if(List.length exp = 0)then raise X_no_match
 else List.hd exp;;
 
 let read_sexprs string = 
   if(String.length string) == 0 then [] 
   else  let(exp,s) = star(nt_remove3dots) (string_to_list string) in exp;;
 end;; 

 
(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)



 #use "reader.ml";;
 open PC;;
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
   val tag_parse_expression : sexpr -> expr 
   val tag_parse_expressions : sexpr list -> expr list
 end;; (* signature TAG_PARSER *)
 
 module Tag_Parser : TAG_PARSER = struct
 
 let reserved_word_list =
   ["and"; "begin"; "cond"; "define"; "else";
    "if"; "lambda"; "let"; "let*"; "letrec"; "or";
    "quasiquote"; "quote"; "set!"; "unquote";
    "unquote-splicing"];;  
 
 (* work on the tag parser starts here *)
 let nt_none_syntax _ = raise X_syntax_error;;
 let disj_syntax nt1 nt2 =
   fun s ->
   try (nt1 s)
   with X_syntax_error -> (nt2 s);;
 
 let disj_list_syntax nts = List.fold_right disj_syntax nts nt_none_syntax;;
 
 let rec make_s sexprlist= 
   match sexprlist with
   | []->Nil
   | _-> Pair(List.hd sexprlist,make_s (List.tl sexprlist));;
  
 
 let rec get_Sexpr_from_quasiquote sexpr=
 match sexpr with
 | Pair(Symbol "unquote",Pair(sexpr,Nil))-> sexpr
 | Pair(Symbol "unquote-splicing",Pair(sexpr,Nil))-> raise X_syntax_error
 | Nil-> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))
 | Symbol _ -> (Pair((Symbol("quote")), (Pair(sexpr, Nil))))
 | Vector(sexpr)->  let vectorList = ( (List.map (fun expr1 -> get_Sexpr_from_quasiquote expr1) sexpr )) in
   (Pair((Symbol("vector")), (make_s vectorList))) 
 | Pair((Pair((Symbol("unquote-splicing")), (Pair(firstsexp, Nil)))),secoundsexp)->let secoundsexp = get_Sexpr_from_quasiquote secoundsexp in
   (Pair((Symbol("append")), (Pair(firstsexp, (Pair(secoundsexp, Nil))))))
 | Pair(firstsexp,(Pair((Symbol("unquote-splicing")), (Pair(secoundsexp, Nil)))))->let firstsexp=get_Sexpr_from_quasiquote firstsexp in
   (Pair((Symbol("cons")),
   (Pair(firstsexp, (Pair(secoundsexp, Nil))))))
 | Pair(firstsexp,secoundsexp)->
   let firstsexp = get_Sexpr_from_quasiquote firstsexp in
     let secoundsexp = get_Sexpr_from_quasiquote secoundsexp in
       (Pair((Symbol("cons")), (Pair(firstsexp, (Pair(secoundsexp, Nil))))))
 | _->sexpr;;   
 
 
 
 let rec cond_expand sexpr=
   match sexpr with
   | Nil->Nil
   | Pair(sexpr1,rest)-> 
     (match sexpr1 with 
     | Pair(Symbol "else",rest1)-> (
       match rest with 
       | Nil->Pair(Symbol "begin",rest1)
       | _-> raise X_syntax_error
       )
     | Pair(exp,Pair(Symbol "=>", rest1))->( 
       match rest with
       | Nil->  Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",Pair(exp,Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,rest1)),Nil)),Nil)),Pair(Pair (Symbol "if",Pair (Symbol "value", Pair (Pair(Pair(Symbol "f",Nil),Pair(Symbol "value",Nil)),Nil))),Nil)))
       | _-> Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",Pair(exp,Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,rest1)),Nil)),Pair(Pair(Symbol "rest",Pair(Symbol "lambda",Pair(Nil,Pair(cond_expand rest,Nil)))),Nil))),Pair(Pair (Symbol "if",Pair (Symbol "value", Pair (Pair(Pair(Symbol "f",Nil),Pair(Symbol "value",Nil)), Pair (Pair(Symbol "rest",Nil), Nil)))),Nil)))
     )
       | Pair(test,rest1)-> (
         match rest with 
         | Nil-> Pair (Symbol "if",Pair (test, Pair (Pair(Symbol "begin",rest1), Nil)))
         | _-> Pair (Symbol "if",Pair (test, Pair (Pair(Symbol "begin",rest1), Pair ((cond_expand rest), Nil))))
       )
     | _->raise X_syntax_error
     )
   | _->raise X_syntax_error
   
 
 let rec  tag_parse_expression sexpr =  disj_list_syntax [cond_tag_parser;mit_define_tag_parser;quote_tag_parser;letrec_tag_parser;and_tag_parser;let_star_tag_parser;let_expansion_tag_parser;begin_tag_parser;or_tag_parser;one_element_tag_parser;if_tag_parser;set_tag_parser;lambda_tag_parser;define_tag_parser;applic_tag_parser]  sexpr and
 
 or_tag_parser sexpr=
   match sexpr with 
   |Pair(Symbol "or",sexplist)->(match sexplist with
     | Nil->Const(Sexpr(Bool(false )))
     |_->(let a = (pair_to_exprlist sexplist) in 
       match List.length a with
       | 1-> List.hd a
       | _-> Or a
        )
     )
   | _->raise X_syntax_error and
 
 set_tag_parser sexpr=
   match sexpr with 
   | Pair(Symbol "set!",Pair(Symbol(name),Pair(sexpr1,Nil)))->Set(tag_parse_expression (Symbol(name)),tag_parse_expression sexpr1)
   | _->raise X_syntax_error and
 
 define_tag_parser sexpr=
   match sexpr with 
   |Pair(Symbol "define",Pair(Symbol(name),Pair(sexpr1,Nil)))->Def(tag_parse_expression (Symbol(name)) ,tag_parse_expression sexpr1)
   | _->raise X_syntax_error and
 
 begin_tag_parser sexpr=
   match sexpr with
   | Pair(Symbol "begin",sexpr)->(
     match sexpr with 
     | Nil->Const(Void)
     | Pair(sexp1,sexp2)-> (match sexp2 with
       |Nil-> let a=pair_to_exprlist (Pair(sexp1,sexp2)) in (match (List.length a) with 
               | 1-> List.hd a
               | _-> Seq a
               )
       |_->Seq (pair_to_exprlist (Pair(sexp1,sexp2)) ))
     |_-> raise X_syntax_error 
   )
 
   |_-> raise X_syntax_error and
 
 applic_tag_parser sexpr=
   match sexpr with
   | Pair(Symbol(x),rest)->(let exprlist=(pair_to_exprlist rest) in
     match List.mem x reserved_word_list with
     | true-> raise X_syntax_error
     | false-> Applic(Var(x), exprlist)
     )
   | Pair(Pair(sexp1,sexp2),Pair(sexp3,sexp4))-> (let exprlist=(pair_to_exprlist (Pair(sexp3,sexp4))) in
     match check_applic_if_lambda (Pair(sexp1,sexp2)) with
     | false ->(let parsed_exp=tag_parse_expression (Pair(sexp1,sexp2)) in Applic(parsed_exp,exprlist))
     | true -> match sexp2 with 
               |Pair(args,body)->  (match is_proper args with
                             |false->let parsed_exp1 = tag_parse_expression (Pair(sexp1,sexp2)) in Applic(parsed_exp1,exprlist)
                             | true-> let a =get_string_if_applic_lambda (Pair(sexp1,sexp2)) in (match ((List.length a)=(List.length exprlist)) with
                                                                                                 | false -> raise X_syntax_error
                                                                                                 | true -> let parsed_exp=tag_parse_expression (Pair(sexp1,sexp2)) in Applic(parsed_exp,exprlist)
                           ))
               | _->raise X_syntax_error
   )
   | Pair(Pair(sexpr1,sexpr2),Nil)-> (let exprlist= (pair_to_exprlist (Pair(Pair(sexpr1,sexpr2),Nil)))  in
     match List.hd exprlist with
     | Const(Sexpr(Symbol(s)))-> (match (List.mem s reserved_word_list  )with
       | true-> raise X_syntax_error
       | false-> Applic(Var(s),List.tl exprlist))
     |_-> Applic(List.hd exprlist,[]))
   | Pair(sexp,rest)->
     (match rest with 
     | Nil->(try Applic(tag_parse_expression sexp,[]) with 
             | X_syntax_error->raise X_syntax_error
           )
     | _-> ( try Applic(tag_parse_expression sexp,pair_to_exprlist rest) with 
             | X_syntax_error->raise X_syntax_error 
           )
     )
   | _->raise  X_syntax_error and
 
 
 check_applic_if_lambda sexpr=
   match sexpr with 
   | Pair(Symbol "lambda", Pair(_arglist, _body))->  true
   | _->false and
 
 get_string_if_applic_lambda sexpr =
   match sexpr with
   |Pair(Symbol "lambda", Pair(_arglist, _body))-> lambda_args_to_string_list _arglist
   | _->[]  and 
 
 if_tag_parser sexpr=
   match sexpr with
   | Pair (Symbol "if",Pair (_test, Pair (_then, Pair (_else, Nil))))-> If ((tag_parse_expression _test), (tag_parse_expression _then ) ,(tag_parse_expression _else ))
   | Pair (Symbol "if", Pair (_test, Pair ( _then, Nil))) -> If ((tag_parse_expression _test), (tag_parse_expression _then ) ,(Const(Void)))
   | _-> raise X_syntax_error  and 
   
 one_element_tag_parser sexpr= 
   match sexpr with
   | Number(x)->Const(Sexpr(Number(x)))
   | Bool(x)->Const(Sexpr(Bool(x)))
   | Char(x)->Const(Sexpr(Char(x)))
   | String(x)->Const(Sexpr(String(x)))
   | Symbol(x)-> (match List.mem x reserved_word_list with
                 |false->Var(x)
                 |true->raise X_syntax_error)
   | Nil->Const(Sexpr(Nil))
   | _->raise X_syntax_error   and
 
 lambda_tag_parser sexpr=
   match sexpr with
   | Pair(Symbol "lambda", Pair(_arglist, _body))-> 
   (match _body with 
   |Nil->raise X_syntax_error
   |_->let args=lambda_args_to_string_list _arglist in
     (match(lambda_args_check args) with
     | false->
       (match (is_proper _arglist) with
         | true-> LambdaSimple ((lambda_args_to_string_list _arglist), single_or_seq( pair_to_exprlist _body))
         | false->let (a,b)= improper_stringList (lambda_args_to_string_list _arglist) in LambdaOpt (a,b, single_or_seq( pair_to_exprlist _body))
       )
     |_->raise X_syntax_error 
     ))
   | _-> raise X_syntax_error    and 
 
 pair_to_exprlist sexpr= 
   match sexpr with
   | Nil->[]
   | Pair(sexp1,rest)-> (tag_parse_expression sexp1)::(pair_to_exprlist rest)
   |_->raise X_syntax_error   and
 
  
 improper_stringList stringlist=
   ((List.rev (List.tl (List.rev stringlist))),List.hd (List.rev stringlist) ) and
 
 single_or_seq list1=
   match List.length list1 with 
   | 1-> List.hd list1
   | 0-> Const(Void)
   | _-> Seq list1 and
 
 is_proper sexpr=
   match sexpr with
   | Nil->true
   | Pair(_,rest)->is_proper rest
   | Symbol(x) ->false
   | _ ->raise X_syntax_error and
 
 lambda_args_to_string_list sexpr=
   match sexpr with
   | Nil->[]
   | Symbol(x)->[x]
   | Pair(Symbol(x),rest)->x:: (lambda_args_to_string_list rest)
   | _->raise X_syntax_error and
 
 lambda_args_check stringlist=
   match stringlist with
   | []->false
   | _-> (
     match List.mem  (List.hd stringlist) (List.tl stringlist) with
     |true->raise X_syntax_error
     |false->lambda_args_check (List.tl stringlist)
   ) and
 
  let_expansion_tag_parser sexp= 
   match sexp with 
   | Pair(Symbol "let",Pair(Nil,body))-> Applic ( LambdaSimple([],single_or_seq(pair_to_exprlist body)),[])
   | Pair(Symbol "let",Pair(args,body))-> let (definitionsnames,exprlist)= definitions_tag_parser args in 
     (match (((List.length definitionsnames) = (List.length exprlist)) && (not(lambda_args_check definitionsnames)) ) with
       | true->Applic ( LambdaSimple(definitionsnames,single_or_seq(pair_to_exprlist body)), exprlist)
       | false-> raise X_syntax_error)
   |  _->raise X_syntax_error and
 
  
 let_star_tag_parser sexp=
   match sexp with 
   | Pair(Symbol "let*",Pair(Nil,body))-> tag_parse_expression(Pair(Symbol "let",Pair(Nil,body)))
   | Pair(Symbol "let*",Pair(args,body))-> 
     (match args with 
     | Pair(Pair(Symbol(x),s1),Nil)->  tag_parse_expression  (Pair(Symbol "let",Pair(args,body)))
     | Pair(Pair(Symbol(x),s1),rest)-> tag_parse_expression (Pair(Symbol "let",Pair(Pair(Pair(Symbol(x), s1),Nil),Pair(Pair(Symbol "let*",Pair(rest,body)),Nil))))
     |_->raise X_syntax_error  
     ) 
   
   |_-> raise X_syntax_error and 
 
 mit_define_tag_parser sexpr=
   match sexpr with
   | Pair(Symbol "define",Pair(Pair(var,arglist),exp))-> tag_parse_expression( Pair(Symbol "define",Pair(var,Pair(Pair(Symbol "lambda", Pair(arglist, exp)),Nil))) )
   |_->raise X_syntax_error and
  
 
 and_tag_parser sexp=
   match sexp with
   | Pair(Symbol "and",Nil)-> Const(Sexpr(Bool(true)))
   | Pair(Symbol "and",Pair(sexp1,rest))-> let a=pair_to_exprlist (Pair(sexp1,rest)) in (match List.length a with
     |1-> List.hd a 
     |_-> tag_parse_expression (Pair (Symbol "if",Pair (sexp1, Pair (Pair(Symbol "and",rest), Pair (Bool false , Nil))))) ) 
   | _->raise X_syntax_error and
 
 
 letrec_tag_parser sexp=
   match sexp with 
   | Pair(Symbol "letrec",Pair(args ,body1))-> let (args,body2)=letrec_tuple args body1 in tag_parse_expression (Pair(Symbol "let",Pair(args,body2)))
   | _-> raise X_syntax_error and
 
   (* (Pair(Symbol "letrec", Pair(Nil, Pair(Symbol "g", Pair(Symbol "f", Nil)))))  *)
 letrec_tuple sexp body1 =
   match sexp with
   | Nil->(Nil,body1)
   | Pair(sexp1,sexp2)->(
     match sexp1 with 
     | Pair(Symbol(x),s1)->let (a,b)=letrec_tuple sexp2 body1 in ((Pair(Pair(Symbol(x),Pair(Symbol "quote",Pair(Symbol "whatever",Nil))),a)), (Pair(Pair(Symbol "set!",Pair(Symbol(x),s1)),b)))
     | _->raise X_syntax_error
   )
   | _->raise X_syntax_error and
 
 cond_tag_parser sexpr =
   match sexpr with 
   | Pair(Symbol "cond",ribs)-> tag_parse_expression (cond_expand ribs)
   | _->raise X_syntax_error and
 
 quote_tag_parser sexpr=
   match sexpr with
   | Pair (Symbol "quote", Pair(sexp,Nil))  -> Const(Sexpr(sexp)) 
   | Pair (Symbol "unquote", Pair(sexp,Nil)) -> raise X_syntax_error 
   | Pair (Symbol "quasiquote", Pair(sexp,Nil)) -> tag_parse_expression (get_Sexpr_from_quasiquote sexp)
   | _->raise X_syntax_error and
   
 definitions_tag_parser sexp=
   match sexp with
   | Nil-> ([],[])
   | Pair(sexp1,sexp2)->(match sexp1 with 
     | Pair (Symbol(x),Pair(s1,Nil))->let (a,b)=definitions_tag_parser sexp2 in (x::a, (tag_parse_expression s1)::b)
     | Pair(Symbol(x),s1)-> let (a,b)=definitions_tag_parser sexp2 in (x::a, (tag_parse_expression s1)::b)
     | _-> raise X_syntax_error )
   | _-> raise X_syntax_error 
 ;;
 let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;
 end;;
 
(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "tag-parser.ml";;
 open Tag_Parser;;
 
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
   | Set' of expr' * expr'
   | Def' of expr' * expr'
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
   | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                             (expr'_eq th1 th2) &&
                                               (expr'_eq el1 el2)
   | (Seq'(l1), Seq'(l2)
   | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
   | (Set'(var1, val1), Set'(var2, val2)
   | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
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
   
                        
 exception X_syntax_error;;
 
 module type SEMANTICS = sig
   val run_semantics : expr -> expr'
   val annotate_lexical_addresses : expr -> expr'
   val annotate_tail_calls : expr' -> expr'
   val box_set : expr' -> expr'
 end;;
 
 module Semantics : SEMANTICS = struct
 let rec find_minor (x,stringlist)= 
   match (String.equal x (List.hd stringlist)) with 
   | true-> 0 
   | false-> (1+ (find_minor (x,List.tl stringlist)));;
   
 let rec make_var_lexical_addresses (x,stringlist,number)=
   match stringlist with
   | []-> VarFree(x)
   | _->(
     match List.mem x (List.hd stringlist) with
     | true->( 
       match number with
       | -1-> VarParam(x,find_minor(x,List.hd stringlist))
       | _-> VarBound(x,number,find_minor(x,List.hd stringlist))
     )
     | false-> make_var_lexical_addresses (x,List.tl stringlist,number+1)
   );;
   
 let rec make_lexical_addresses (expr ,stringlist)=
   match expr with 
   | Const(x)->Const'(x)
   | If (expr1, expr2 ,expr3) -> If'( (make_lexical_addresses (expr1 ,stringlist)),(make_lexical_addresses (expr2 ,stringlist)),(make_lexical_addresses (expr3 ,stringlist)))
   | Seq(exprlist)-> Seq' (List.map  make_lexical_addresses (List.map  (fun (x)->(x,stringlist)) exprlist ))
   | Set(expr1,expr2)-> Set' ((make_lexical_addresses (expr1 ,stringlist)),(make_lexical_addresses (expr2 ,stringlist)))
   | Def(expr1,expr2)-> Def' ((make_lexical_addresses (expr1 ,stringlist)),(make_lexical_addresses (expr2 ,stringlist)))
   | Or(exprlist)-> Or' (List.map  make_lexical_addresses (List.map  (fun (x)->(x,stringlist)) exprlist ))
   | Applic(expr1,exprlist)-> Applic' ((make_lexical_addresses (expr1 ,stringlist)),(List.map  make_lexical_addresses (List.map  (fun (x)->(x,stringlist)) exprlist )))
   | LambdaSimple (stringlistparams,expr)-> LambdaSimple' (stringlistparams,make_lexical_addresses(expr,stringlistparams::stringlist))
   | LambdaOpt(stringlistparams,s,expr)-> LambdaOpt' (stringlistparams,s, make_lexical_addresses(expr, (stringlistparams@ [s])::stringlist))
   | Var(x)-> Var' (make_var_lexical_addresses (x,stringlist,-1));;
 
 let annotate_lexical_addresses e = make_lexical_addresses(e,[]);;
 
 let rec  make_applic_tp (e,inlambda)=
   match e with  
   | If' (expr1,expr2,expr3)->
     (match inlambda with
       | false-> If'(make_applic_tp(expr1,false),make_applic_tp (expr2,false),make_applic_tp (expr3,false))
       | true-> If'(make_applic_tp(expr1,false),make_applic_tp (expr2,true),make_applic_tp (expr3,true))
     )
   | Seq'(exprlist)-> (
       match inlambda with
       | false-> Seq'(List.map make_applic_tp (List.map  (fun (x)->(x,false)) exprlist))
       | true-> Seq' ((List.map make_applic_tp (List.map  (fun (x)->(x,false)) (List.rev (List.tl (List.rev exprlist)))))@ [make_applic_tp(List.hd (List.rev exprlist),true)])
     )
   | Set'(expr1,expr2)-> Set'(make_applic_tp(expr1,false),make_applic_tp(expr2,false))
   | Def'(expr1,expr2)-> Def'(make_applic_tp(expr1,false),make_applic_tp(expr2,false))
   | Or'(exprlist)->(
       match inlambda with
       | false-> Or'(List.map make_applic_tp (List.map  (fun (x)->(x,false)) exprlist))
       | true-> Or' ((List.map make_applic_tp (List.map  (fun (x)->(x,false)) (List.rev (List.tl (List.rev exprlist)))))@ [make_applic_tp(List.hd (List.rev exprlist),true)])
     )
   | LambdaSimple'(parmslist,expr)->LambdaSimple'(parmslist,make_applic_tp(expr,true))
   | LambdaOpt'(parmslist,optstring,expr)->LambdaOpt'(parmslist,optstring,make_applic_tp(expr,true))
   | Applic' (expr,exprlist)-> 
     (match inlambda with
      | false-> Applic'(make_applic_tp (expr,false), (List.map make_applic_tp (List.map  (fun (x)->(x,false)) exprlist)))
      | true-> ApplicTP'(make_applic_tp (expr,false), (List.map make_applic_tp (List.map  (fun (x)->(x,false)) exprlist)))
     )
   | _->e;;
 
     
     
     ;;
 let  annotate_tail_calls e = make_applic_tp (e,false);;
 
 let check_get parm body =
   let unique = 
     let last = ref 0 in fun () -> incr last ; !last in
   
   let rec check_get_helper parm body numberlist  = 
     match body with
   | If' (expr1, expr2, expr3)-> (check_get_helper parm expr1 numberlist )@(check_get_helper parm expr2 numberlist )@(check_get_helper parm expr3 numberlist )
   | Def' (expr1, expr2) -> (check_get_helper parm expr1 numberlist)@(check_get_helper parm expr2 numberlist)
   | Seq' exprlist -> List.flatten  (List.map (fun(body)-> check_get_helper parm body numberlist)  exprlist)
   | Set' (Var'(_),expr)->  (check_get_helper parm expr numberlist)
   | BoxSet' (_, expr) -> check_get_helper parm expr numberlist
   | Or' exprlist ->  List.flatten  (List.map (fun(body)-> check_get_helper parm body numberlist)  exprlist)
   | Applic' (op, exprlist) | ApplicTP' (op, exprlist) -> (check_get_helper parm op numberlist)@ (List.map List.flatten  (List.map (fun(body)-> check_get_helper parm body numberlist)  exprlist))
   | LambdaSimple' (parmlist,body1)-> if (List.mem parm parmlist  ) then ([]) else let num = unique() in(check_get_helper parm body1 (num::numberlist))
   | LambdaOpt' (parmlist,opt,body1)-> if (List.mem parm (opt::parmlist)  ) then ([]) else let num = unique() in (check_get_helper parm body1 (num::numberlist))
   | Var'(VarBound(name,minor,major))-> if (parm=name) then [numberlist] else ([])
   | Var'(VarParam(name,minor))-> if (parm=name) then [numberlist] else ([])
   | _->[] in
   (check_get_helper parm body [0] )
   ;;
 
 
   let check_set parm body =
     let unique = 
       let last = ref 0 in fun () -> incr last ; !last in
     
     let rec check_set_helper parm body numberlist  = 
       match body with
     | If' (expr1, expr2, expr3)-> (check_set_helper parm expr1 numberlist )@(check_set_helper parm expr2 numberlist )@(check_set_helper parm expr3 numberlist )
     | Def' (expr1, expr2) -> (check_set_helper parm expr1 numberlist)@(check_set_helper parm expr2 numberlist)
     | Seq' exprlist -> List.flatten  (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist)
     | Set' (Var'(VarBound(name,minor,major)),expr)-> if (parm=name) then ([numberlist]@ (check_set_helper parm expr numberlist)) else ((check_set_helper parm expr numberlist))
     | Set' (Var'(VarParam (name,major)),expr)-> if (parm=name) then ([numberlist]@ (check_set_helper parm expr numberlist)) else ((check_set_helper parm expr numberlist))
     | Set' (Var'(VarFree(x)),expr)-> (check_set_helper parm expr numberlist)
     | BoxSet' (_, expr) -> check_set_helper parm expr numberlist
     | Or' exprlist ->  List.flatten  (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist)
     | Applic' (op, exprlist) | ApplicTP' (op, exprlist) -> (check_set_helper parm op numberlist)@ (List.map List.flatten  (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist))
     | LambdaSimple' (parmlist,body1)-> if (List.mem parm parmlist  ) then ([]) else let num = unique() in(check_set_helper parm body1 (num::numberlist))
     | LambdaOpt' (parmlist,opt,body1)-> if (List.mem parm (opt::parmlist)  ) then ([]) else let num = unique() in (check_set_helper parm body1 (num::numberlist))
     | Var'(VarBound(name,minor,major))-> if (parm=name) then [] else ([])
     | Var'(VarParam(name,minor))-> if (parm=name) then [] else ([])
     | _->[] in
     
     (check_set_helper parm body [0] )
     ;;
 
  let check_combination (x,y)=
   let lastone =(List.hd x != List.hd y)  in
   let rec common_ancestor (x,y)=
    if (y=[] || x=[]) then true  else (
      match List.hd x = List.hd y with
      | true->  false
      | false ->common_ancestor (List.tl x,List.tl y)
    ) in
   ( lastone && common_ancestor (List.tl (List.rev x),List.tl (List.rev y)) )
   ;;
 
 let check_if_should_box_parm (parm ,body)=
   let setlist= List.filter (fun(x)->x!=[]) (check_set parm body)  in
     let getlist= List.filter (fun(x)->x!=[]) (check_get parm body)  in
       let combinationlist= List.concat (List.map (fun(x)->List.map (fun(y)->(x,y)) getlist) setlist) in
         if (ormap check_combination combinationlist) then parm else "";;
 
 
 let checklambdaparms parmslist body=
   let list1= List.map check_if_should_box_parm (List.map (fun(x)-> (x,body)) parmslist) in
     let list2= List.filter (fun(x)->x!="") list1 in
       list2;; 
 
 let rec parmstoset parmlisttobox parmListwithminor =
   if (parmListwithminor = []) then [] 
     else (
       let (a,b)=List.hd parmListwithminor in
         if(List.mem a parmlisttobox ) then ((a,b)::(parmstoset parmlisttobox (List.tl parmListwithminor ))) 
           else ((parmstoset parmlisttobox (List.tl parmListwithminor )))
     )
   ;;
 
 let makeindexlist length=
   let rec makeindex number=
     if(number=length) then [] else (number::makeindex(number+1)) in
   makeindex 0;;
 
 let makebodyprefix parmList  newparmstobox =
   let parmListwithminor= List.map2 (fun x y->(x,y)) parmList (makeindexlist (List.length parmList)) in
       let  parmswithminortoset= parmstoset newparmstobox parmListwithminor in
         List.map (fun (a,b)->Set' (Var'(VarParam(a,b)),Box'(VarParam(a,b)))) parmswithminortoset
 
 ;;
 
 let rec box_set_helper (e,stringlist)=
   match e with
   | Const' _  | Box' _ | BoxGet' _ | Var'(VarFree(_)) -> e
   | Var' (VarBound(name,minor,major))->
     if (List.mem  name stringlist) then ( BoxGet'(VarBound(name,minor,major))) else (e)
   | Var'(VarParam(name,x))->
     if (List.mem  name stringlist) then ( BoxGet'(VarParam(name,x))) else (e)
   | BoxSet' (var, expr) -> BoxSet' (var, box_set_helper (expr ,stringlist))
   | Def'(expr1,expr2)-> Def'(box_set_helper (expr1 ,stringlist),box_set_helper (expr2 ,stringlist))
   | If' (expr1,expr2,expr3)-> If' (box_set_helper (expr1 ,stringlist),box_set_helper (expr2 ,stringlist),box_set_helper (expr3 ,stringlist))
   | Seq'(exprlist)-> Seq'(List.map box_set_helper (List.map  (fun(x)->(x,stringlist)) exprlist ) )
   | Set'(Var'(VarBound(name,minor,major)),expr2)-> 
     if (List.mem  name stringlist) then BoxSet'(VarBound(name,minor,major),box_set_helper (expr2,stringlist)) else (Set'(Var'(VarBound(name,minor,major)),box_set_helper (expr2,stringlist)))
   | Set'(Var'(VarParam(name,minor)),expr2)->
     if (List.mem  name stringlist) then BoxSet'(VarParam(name,minor),box_set_helper (expr2,stringlist)) else (Set'(Var'(VarParam(name,minor)),box_set_helper (expr2,stringlist)))
   | Set'(Var'(VarFree(name)),expr2)-> Set'(Var'(VarFree(name)),box_set_helper (expr2,stringlist))
   | Or'(exprlist)-> Or' (List.map box_set_helper (List.map  (fun(x)->(x,stringlist)) exprlist ) )
   | Applic'(expr1,exprlist) -> Applic'(box_set_helper (expr1,stringlist),(List.map box_set_helper (List.map  (fun(x)->(x,stringlist)) exprlist ) ))
   | ApplicTP'(expr1,exprlist)-> ApplicTP'(box_set_helper (expr1,stringlist),(List.map box_set_helper (List.map  (fun(x)->(x,stringlist)) exprlist ) ))
   | LambdaSimple' (parmlist,body)-> 
     (let new_string_list= List.filter (fun(x)-> not (List.mem x parmlist)) stringlist in
       let newparmstobox= checklambdaparms parmlist body in
         let prefixtoadd= makebodyprefix parmlist  newparmstobox in
           let body1= box_set_helper (body ,(newparmstobox@new_string_list)) in
             (match prefixtoadd@[body1] with
               | []-> LambdaSimple'(parmlist,Const' Void)
               | x::[]->LambdaSimple'(parmlist,x)
               | other->LambdaSimple'(parmlist,Seq' other))
     )
   | LambdaOpt' (parmlist,opt,body)->
     (let new_string_list= List.filter (fun(x)-> not (List.mem x parmlist)) stringlist in
       let newparmstobox= checklambdaparms (opt::parmlist) body in
         let prefixtoadd= makebodyprefix (parmlist@[opt])  newparmstobox in
           let body1= box_set_helper (body ,(newparmstobox@new_string_list)) in
             (match prefixtoadd@[body1] with
               | []-> LambdaOpt'(parmlist,opt,Const' Void)
               | x::[]->LambdaOpt'(parmlist,opt,x)
               | other->LambdaOpt'(parmlist,opt,Seq' other)
             )
     )
   | _-> raise X_this_should_not_happen
   ;;
 
 let box_set e = box_set_helper (e,[]);;
 
 let run_semantics expr = 
     box_set  
     (      
       annotate_tail_calls
        (annotate_lexical_addresses expr));;
 end;; (* struct Semantics *)
 
#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' ->int->int-> string
end;;

module Code_Gen : CODE_GEN = struct

  let primitive_names_to_labels = 
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
      "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
      "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
      "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
      "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
      "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
      "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
      "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"
      ;"car","car";"cdr","cdr";"set-car!","set_car"; "set-cdr!" ,"set_cdr";"cons","cons" ;"apply","apply"(* you can add yours here *)];;

  let remove_duplicates_constant_helper e l =
    let rec loop l acc = match l with
      | [] -> List.rev acc
      | x::xs ->
        (match (e,x) with 
        | (_,Void)->  loop xs (x::acc)
        | (Void,_)->  loop xs (x::acc)
        | (Sexpr(e1),Sexpr(x1)) when sexpr_eq e1  x1 -> loop xs acc
        | _-> loop xs (x::acc)) in 
    loop l [];;

  let rec remove_duplicates_constant l acc =
    match l with
    | [] -> List.rev acc
    | x :: xs -> remove_duplicates_constant (remove_duplicates_constant_helper x xs) (x::acc);;


  let rec get_offset_of_const list2 sexpr1=
    
    match  list2 with
    | []->raise X_not_yet_implemented
    | _-> 
      match sexpr1 with 
      | Void -> 0
      | Sexpr(Nil) -> 1
      | Sexpr(Bool true) -> 2
      | Sexpr(Bool false) -> 4
      | Sexpr(x)->  let (a,(number,b))=(List.hd list2) in
        (match a with 
        |Void -> get_offset_of_const (List.tl list2) sexpr1
        | Sexpr(a)->
          (match sexpr_eq a x with 
          | true->  number
          | false-> get_offset_of_const (List.tl list2) sexpr1))
      
        

  let string_to_ints_of_chars string =
    let charlist = string_to_list string in
     ( String.concat "," (List.map (fun c->string_of_int(Char.code c)) charlist))
  
  let get_labels ((con1,number) ,list2)= 
  match con1 with 
  | Void-> (con1,(number,"MAKE_VOID"))
  | Sexpr(Bool(true))-> (con1,(number,"MAKE_BOOL(1)"))
  | Sexpr(Bool(false))-> (con1,(number,"MAKE_BOOL(0)"))
  | Sexpr(Nil)-> (con1,(number,"MAKE_NIL"))
  | Sexpr(Number(Int(x)))-> (con1,(number,"MAKE_LITERAL_INT("^(string_of_int(x))^")"))
  | Sexpr(Number(Float(x)))-> (con1,(number,"MAKE_LITERAL_FLOAT("^string_of_float(x)^")"))
  | Sexpr(Char(x))-> (con1,(number,"MAKE_LITERAL_CHAR("^(string_of_int(int_of_char x))^")"))
  | Sexpr (String(x))-> (con1,(number,"MAKE_LITERAL_STRING "^(string_to_ints_of_chars x)))
  | Sexpr (Symbol(x))-> let number1= get_offset_of_const list2 (Sexpr (String(x))) in let s1= "const_tbl+"^string_of_int(number1) in (con1,(number,"MAKE_LITERAL_SYMBOL("^s1^")"))
  | Sexpr(Pair(car,cdr))->  
    let (string1,string2)= ("const_tbl+"^ string_of_int(get_offset_of_const list2 (Sexpr(car))),"const_tbl+"^ string_of_int(get_offset_of_const list2 (Sexpr(cdr)))) in
    (con1,(number,"MAKE_LITERAL_PAIR("^string1^","^string2^ ")"))
  | Sexpr(Vector(sexprlist))-> let stringList= List.map (fun x-> "const_tbl+"^ string_of_int(get_offset_of_const list2 (Sexpr(x)))) sexprlist in 
    match sexprlist with 
    |[]->(con1,(number,"MAKE_LITERAL_VECTOR "))
    |_-> let arguments=" "^(List.hd stringList)^List.fold_left (fun x y-> x^","^y) "" (List.tl stringList) in
         (con1,(number,"MAKE_LITERAL_VECTOR"^arguments^""));;
  

  let  rec get_const_tuple list1 list2=
    match list1 with 
    | []->list2
    | _-> (get_const_tuple (List.tl list1) (list2@[get_labels ((List.hd list1) ,list2)]));;


  let get_offset_toadd number con1 =
    match con1 with 
    | Void-> number+1
    | Sexpr(Bool(x))-> number+2
    | Sexpr(Nil)-> number+1
    | Sexpr(Number(x))-> number +9
    | Sexpr(Char(x))-> number +2
    | Sexpr (String(x))-> number+9+ (String.length x)
    | Sexpr (Symbol(x))-> number+9
    | Sexpr(Pair(car,cdr))-> number+17
    | Sexpr(Vector(sexprlist))->number+9+ (List.length sexprlist)*8  ;;

  let rec const_with_offset  list1 list2=
   match list1 with
   | []->list2
   | _ -> let(a,b)= (List.hd(List.rev list2)) in const_with_offset (List.tl list1 ) (list2@[(List.hd list1,(get_offset_toadd b a))]);;

  let rec expand_pair_constants (sexpr ,array1)=
    match sexpr with 
    | Pair(a1,b1)->  let ((a,b),(c,d))= ((expand_pair_constants(a1,[])),(expand_pair_constants(b1,[]))) in ((a@c),(d@b@[Sexpr(Pair(a1,b1))]))
    | Vector(exprList)-> let (list1,list2)= ((List.map (fun (a,b)-> a)((List.map expand_pair_constants (List.map (fun(x)->(x,[])) exprList)))),(List.map (fun (a,b)-> b)((List.map expand_pair_constants (List.map (fun(x)->(x,[])) exprList))))) in
      ((List.flatten list1), array1@(List.flatten list2)@[Sexpr(Vector(exprList))])
    | (Symbol(x))-> (([Sexpr(String(x))]@[Sexpr(Symbol(x))]),[])
    | _-> ([Sexpr(sexpr)],[]) ;;
 
  let rec get_constant_list expression=
    match expression with 
    | Var'(_) | Box' (_) |  BoxGet'(_)-> []
    | Const'(Sexpr(Pair(car,cdr)))-> let (a,b)=(expand_pair_constants ((Pair(car,cdr)),[])) in  (a@b)
    | Const'(Sexpr(Vector(exprlist)))->  let (a,b)=expand_pair_constants ((Vector(exprlist)),[]) in  (a@b)
    | Const'(Sexpr(Symbol(x)))-> [Sexpr(String(x))]@[Sexpr(Symbol(x))]
    | Const'(Sexpr(con))-> [(Sexpr(con))]
    | Const'(Void)-> [Void]
    | BoxSet' (v,expr)->  (get_constant_list expr)
    | If' (expr1,expr2,expr3)-> (get_constant_list expr1)@(get_constant_list expr2)@(get_constant_list expr3)
    | Seq'(exprList)-> (List.flatten (List.map get_constant_list exprList))
    | Or'(exprList)-> (List.flatten (List.map get_constant_list exprList))
    | Def'(expr1,expr2)-> (get_constant_list expr1)@(get_constant_list expr2)
    | Set' (expr1,expr2)-> (get_constant_list expr1)@(get_constant_list expr2)
    | LambdaSimple'(stringlist,expr)-> (get_constant_list expr)
    | LambdaOpt'(stringlist,s,expr)-> (get_constant_list expr)
    | Applic'(expr1,exprlist)-> (get_constant_list expr1)@ (List.flatten (List.map get_constant_list exprlist))
    | ApplicTP'(expr1, exprlist)->(get_constant_list expr1)@ (List.flatten (List.map get_constant_list exprlist));;

  let make_consts_tbl asts = 
    let cons_table= (([Void]@[Sexpr(Nil)]@[Sexpr(Bool(true))]@[Sexpr(Bool(false))])@(List.flatten (List.map get_constant_list asts))) in
      let cons_table= remove_duplicates_constant cons_table [] in 
        let cons_table_with_offset= (const_with_offset (List.tl cons_table) [((List.hd cons_table),0)]) in
          let cons_table=(get_const_tuple cons_table_with_offset [])  in
            cons_table;;

  let rec get_FreeVar_list expression=
    match expression with 
    | Var'(VarFree(x))->[x]
    | Box' (_) | Var'(_) |  BoxGet'(_) | Const'(_)-> []
    | BoxSet' (v,expr)->  (get_FreeVar_list expr)
    | If' (expr1,expr2,expr3)-> (get_FreeVar_list expr1)@(get_FreeVar_list expr2)@(get_FreeVar_list expr3)
    | Seq'(exprList)-> (List.flatten (List.map get_FreeVar_list exprList))
    | Or'(exprList)-> (List.flatten (List.map get_FreeVar_list exprList))
    | Def'(expr1,expr2)-> (get_FreeVar_list expr1)@(get_FreeVar_list expr2)
    | Set' (expr1,expr2)-> (get_FreeVar_list expr1)@(get_FreeVar_list expr2)
    | LambdaSimple'(stringlist,expr)-> (get_FreeVar_list expr)
    | LambdaOpt'(stringlist,s,expr)-> (get_FreeVar_list expr)
    | Applic'(expr1,exprlist)-> (get_FreeVar_list expr1)@ (List.flatten (List.map get_FreeVar_list exprlist))
    | ApplicTP'(expr1, exprlist)->(get_FreeVar_list expr1)@ (List.flatten (List.map get_FreeVar_list exprlist));;
  
  let makeindexlist length=
    let rec makeindex number=
      if(number=length) then [] else (number::makeindex(number+1)) in
    makeindex 0;;
let a (b,c)= b;;
 
let make_fvars_tbl asts = let freevars= (List.map a primitive_names_to_labels)@(List.flatten (List.map get_FreeVar_list asts)) in 
  List.map2 (fun x y->(x,y)) freevars (makeindexlist (List.length freevars));;
(* ****************************************************************** generate function ************************************************************* *)
(* val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string *)
let rec get_offset_of_freevar list2 const=
  let (a,b)=List.hd list2 in if (String.equal a const) then (b) else ( get_offset_of_freevar (List.tl list2) const);;

let rec generate consts fvars e number1 depthOfLambda= 
  let unique = 
    let last = ref 0 in fun () -> incr last ; !last in
  let rec generate_helper consts fvars e number1 depthOfLambda= 
    match e with 
    | Box'(var)-> (generate_helper consts fvars (Var'(var)) number1 depthOfLambda)^
                "MALLOC r8, 8 \n
                mov [r8], rax \n
                mov rax,r8 \n"
    | Const'(x)-> "mov rax, const_tbl+"^string_of_int(get_offset_of_const consts x)^"\n"
    | Var'(VarParam(_,minor))->"mov rax, qword[rbp+8*(4+"^(string_of_int minor)^")]\n"
    | Var'(VarFree(s))-> "mov rax, FVAR("^(string_of_int(get_offset_of_freevar fvars s))^")\n"
    | Set'(Var'(VarParam(_,minor)),expr)-> ";box' start\n"^(generate_helper consts fvars expr number1 depthOfLambda)^";box' end\n"^ "mov qword[rbp+8*(4+"^(string_of_int minor)^")], rax \n"^"mov rax, SOB_VOID\n"
    | Var'(VarBound(s,major,minor))->"mov rax, qword [rbp + 8 * 2] \n"^"mov rax, qword [rax + 8 * "^(string_of_int major)^"] \n"^"mov rax, qword [rax + 8 * "^(string_of_int minor)^"] \n"
    | Set'(Var'(VarBound(s,major,minor)),expr)-> (generate_helper consts fvars expr number1 depthOfLambda)^"mov rbx, qword[rbp+8*2] \n"^"mov rbx, qword[rbx+8*"^(string_of_int major)^"]\n"^"mov qword [rbx + 8 * "^(string_of_int minor)^"], rax \n"^"mov rax, SOB_VOID \n"
    | Set'(Var'(VarFree(s)),expr)-> (generate_helper consts fvars expr number1 depthOfLambda)^ "mov FVARLABEL("^(string_of_int(get_offset_of_freevar fvars s))^"), rax \n"^"mov rax, SOB_VOID \n"
    | Seq'(exprlist)->(
      match List.length exprlist with  
      |0->""
      |_->List.fold_left (fun x y-> x^y) "" (List.map (fun x->generate_helper consts fvars x number1 depthOfLambda) exprlist)
    )
    | Or'(exprlist)->(
      match List.length exprlist with  
      |0->""
      |_->(let number=unique() in (List.fold_left (fun x y-> x^"cmp rax, SOB_FALSE \n"^"jne Lexit"^(string_of_int number1)^(string_of_int number) ^" \n"^y) ((generate_helper consts fvars ( List.hd exprlist) number1 depthOfLambda)^"\n cmp rax, SOB_FALSE \n"^"jne Lexit"^(string_of_int number1)^(string_of_int number) ^" \n") (List.map (fun x->generate_helper consts fvars x number1 depthOfLambda)( List.tl exprlist)) )^ "Lexit"^(string_of_int number1)^(string_of_int number) ^": \n")
    )
    | If'(expr1,expr2,expr3)-> let number=unique() in ";IF TEST\n"^(generate_helper consts fvars expr1 number1 depthOfLambda)^ "cmp rax, SOB_FALSE \n"^"je Lelse"^(string_of_int number1)^(string_of_int number) ^" \n"^";IF THEN\n"^(generate_helper consts fvars expr2 number1 depthOfLambda)^ "jmp Lexit"^(string_of_int number1)^(string_of_int number) ^" \n"^";IF ELSE\n"^"Lelse"^(string_of_int number1)^(string_of_int number) ^":\n"^ (generate_helper consts fvars expr3 number1 depthOfLambda)^ "Lexit"^(string_of_int number1)^(string_of_int number) ^": \n"
    | BoxGet'(anyVar)-> (generate_helper consts fvars (Var'(anyVar)) number1 depthOfLambda)^ "mov rax, qword[rax] \n"
    | BoxSet'(anyVar,expr)->(generate_helper consts fvars expr number1 depthOfLambda)^"push rax \n"^(generate_helper consts fvars (Var'(anyVar)) number1 depthOfLambda)^ "pop qword [rax]\n"^ "mov rax, SOB_VOID\n"
    | LambdaSimple'(stringlist,body)->  let number=unique() in
      ( match depthOfLambda with 
      | 0->
        "MAKE_CLOSURE(rax, SOB_NIL, Lcode"^(string_of_int number1)^(string_of_int number) ^")\n"^
        "jmp Lcont"^(string_of_int number1)^(string_of_int number) ^"\n\n"^
        
        "Lcode"^(string_of_int number1)^(string_of_int number) ^":\n"^
        "push rbp\n"^
        "mov rbp,rsp\n"^
        (generate_helper consts fvars body number1 (depthOfLambda+1))^
        "leave\n"^
        "ret\n\n"^
        "Lcont"^(string_of_int number1)^(string_of_int number) ^":\n"

      |_->
        "MALLOC r8, "^(string_of_int((depthOfLambda+1)*8))^"\n"^
        "mov r9, qword[rbp+8*2]"^"\n"^
        "mov rcx,"^(string_of_int(depthOfLambda))^"\n"^  (*1*)
        "mov r10,rcx\n\n"^ (* 1 *)

        "copy_env"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
        "dec rcx"^"\n"^
        "mov r11,qword[r9+rcx*8]\n"^
        "inc rcx"^"\n"^
        "mov qword[r8+r10*8],r11\n"^
        "dec r10\n"^
        "loop copy_env"^(string_of_int number1)^(string_of_int number) ^", rcx\n\n"^

        "mov rax,qword[rbp+3*8]"^"\n"^
        "mov r11,8"^"\n"^
        "mul r11"^"\n"^
        "MALLOC r13,rax\n"^
        "mov rcx,qword[rbp+3*8]\n"^
        "mov r11,4\n"^
        "mov r12,0\n\n"^
        
        "cmp rcx,0"^"\n"^
        "je skip_copy_parm"^(string_of_int number1)^(string_of_int number) ^"\n"^

        "copy_parms_into_vector"^(string_of_int number1)^(string_of_int number) ^":\n"^
        "mov r10,qword[rbp+r11*8]\n"^
        "mov qword[r13+r12*8],r10\n"^
        "inc r12\n"^
        "inc r11\n"^
        "loop copy_parms_into_vector"^(string_of_int number1)^(string_of_int number) ^",rcx\n\n"^

        "skip_copy_parm"^(string_of_int number1)^(string_of_int number) ^":\n"^

        "mov qword[r8],r13\n"^
        "MAKE_CLOSURE(rax, r8, Lcode"^(string_of_int number1)^(string_of_int number) ^")\n"^
        "jmp Lcont"^(string_of_int number1)^(string_of_int number) ^"\n\n"^
        "Lcode"^(string_of_int number1)^(string_of_int number) ^":\n"^
        "push rbp\n"^
        "mov rbp,rsp\n"^
        (generate_helper consts fvars body number1 (depthOfLambda+1))^
        "leave\n"^
        "ret\n\n"^
        "Lcont"^(string_of_int number1)^(string_of_int number) ^":\n"
      )
    | Def'(expr1,expr2)->(
      match expr1 with
      | Var'(VarFree(s))-> (generate_helper consts fvars (Set'(expr1,expr2)) number1 depthOfLambda)
      | _->raise X_this_should_not_happen
    )
    | Applic'(expr,exprlist)->(
      match exprlist with
      | []-> 
        "push 0\n"^
        (generate_helper consts fvars expr number1 depthOfLambda)^"\n"^ 
        "CLOSURE_ENV rcx ,rax\n"^
        "push rcx\n"^
        "CLOSURE_CODE rcx ,rax\n"^
        "call rcx\n"^
        "add rsp , 8*1\n"^
        "pop rbx\n"^
        "shl rbx , 3\n"^
        "add rsp , rbx\n"
      | _-> 
        (let exprlist=(List.map (fun x->(generate_helper consts fvars x number1 depthOfLambda)^ "push rax\n") (List.rev exprlist)) in
        ((List.fold_left (fun x y-> x^y) "" exprlist)^
          "push "^(string_of_int(List.length exprlist))^"\n"^
          (generate_helper consts fvars expr number1 depthOfLambda)^"\n"^ 
          "CLOSURE_ENV rcx ,rax\n"^
          "push rcx\n"^
          "CLOSURE_CODE rcx ,rax\n"^
          "call rcx\n"^
          "add rsp , 8*1\n"^
          "pop rbx\n"^
          "shl rbx , 3\n"^
          "add rsp , rbx\n"  
          )
        )
    )
    | LambdaOpt'(stringlist,stringopt,body)->(  
      let number=unique() in
        match depthOfLambda with 
        | 0->(
          "MAKE_CLOSURE(rax, SOB_NIL, Lcode"^(string_of_int number1)^(string_of_int number) ^")\n"^
          "jmp Lcont"^(string_of_int number1)^(string_of_int number) ^"\n\n"^

          "Lcode"^(string_of_int number1)^(string_of_int number) ^":\n"^
          "push rbp\n"^
          "mov rbp,rsp\n"^
          "mov r9,[rbp+3*8]"^"\n"^(*[rbp+3*8] *)
          "cmp r9,"^(string_of_int(List.length stringlist))^"\n"^
          "je add_empty_list"^(string_of_int number1)^(string_of_int number) ^"\n\n"^

          "put_args_in_list"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^ 
          "mov r10,"^(string_of_int((List.length stringlist)))^"\n"^
          "sub r9,r10"^"\n"^
          "mov rcx,r9"^"\n"^
          "dec rcx"^"\n"^
          "mov r9,[rbp+3*8]"^"\n"^ (*[rbp+3*8] *)
          "add r9,3"^"\n"^
          "shl r9,3"^"\n"^
          "add r9,rbp"^"\n"^
          "mov r11, qword[r9]"^"\n"^
          "MAKE_PAIR(r15,r11,SOB_NIL)"^"\n"^
          "mov r12,r15"^"\n"^
          "sub r9, 8"^"\n"^
          "cmp rcx, 0"^"\n"^
          "je cont"^(string_of_int number1)^(string_of_int number)^"\n\n"^

          "loop"^(string_of_int number1)^(string_of_int number)^":"^"\n"^
          "mov r11, qword[r9]"^"\n"^
          "MAKE_PAIR(r15,r11,r12)"^"\n"^
          "mov r12,r15"^"\n"^
          "sub r9, 8"^"\n"^
          "loop loop"^(string_of_int number1)^(string_of_int number) ^", rcx"^"\n\n"^

          "cont"^(string_of_int number1)^(string_of_int number)^":\n"^
          "add r9, 8"^"\n"^
          "mov qword[r9],r12"^"\n"^
          "jmp continue"^(string_of_int number1)^(string_of_int number) ^"\n\n"^

          "add_empty_list"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          "mov qword[rbp+3*8],"^(string_of_int((List.length stringlist)+1))^"\n"^
          "sub rbp,8"^"\n"^
          "sub rsp,8\n"^
          "mov rcx,"^(string_of_int((List.length stringlist)+4))^"\n"^
          "mov r12,rbp"^"\n"^
          "add r12,8"^"\n\n"^

          "shift_down"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          "mov r8,qword[r12]"^"\n"^
          "sub r12,8"^"\n"^
          "mov qword[r12],r8"^"\n"^
          "add r12,16"^"\n"^
          "loop shift_down"^(string_of_int number1)^(string_of_int number)^",rcx"^"\n\n"^

          "sub r12,8"^"\n"^
          "mov r10, SOB_NIL "^"\n"^
          "mov qword[r12],r10"^"\n"^ 
          "continue"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          
          (generate_helper consts fvars body number1 (depthOfLambda+1))^
          "leave\n"^
          "ret\n\n"^

          "Lcont"^(string_of_int number1)^(string_of_int number) ^":\n"
        )
        |_->(
          "MALLOC r8, "^(string_of_int((depthOfLambda+1)*8))^"\n"^
          "mov r9, qword[rbp+8*2]"^"\n"^
          "mov rcx,"^(string_of_int(depthOfLambda))^"\n"^  (*1*)
          "mov r10,rcx\n\n"^ (* 1 *)

          "copy_env"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          "dec rcx"^"\n"^
          "mov r11,qword[r9+rcx*8]\n"^
          "inc rcx"^"\n"^
          "mov qword[r8+r10*8],r11\n"^
          "dec r10\n"^
          "loop copy_env"^(string_of_int number1)^(string_of_int number) ^", rcx\n\n"^

          "mov rax,qword[rbp+3*8]"^"\n"^
          "mov r11,8"^"\n"^
          "mul r11"^"\n"^
          "MALLOC r13,rax\n"^
          "mov rcx,qword[rbp+3*8]\n"^
          "mov r11,4\n"^
          "mov r12,0\n\n"^

          "cmp rcx,0"^"\n"^
          "je skip_copy_parm"^(string_of_int number1)^(string_of_int number) ^"\n"^

          "copy_parms_into_vector"^(string_of_int number1)^(string_of_int number) ^":\n"^
          "mov r10,qword[rbp+r11*8]\n"^
          "mov qword[r13+r12*8],r10\n"^
          "inc r12\n"^
          "inc r11\n"^
          "loop copy_parms_into_vector"^(string_of_int number1)^(string_of_int number) ^",rcx\n\n"^

        "skip_copy_parm"^(string_of_int number1)^(string_of_int number) ^":\n"^

          "mov qword[r8],r13\n"^
          "MAKE_CLOSURE(rax, r8, Lcode"^(string_of_int number1)^(string_of_int number) ^")\n"^
          "jmp Lcont"^(string_of_int number1)^(string_of_int number) ^"\n\n"^
          
          "Lcode"^(string_of_int number1)^(string_of_int number) ^":\n"^
          "push rbp\n"^
          "mov rbp,rsp\n"^
          "mov r9,[rbp+3*8]"^"\n"^(*[rbp+3*8] *)
          "cmp r9,"^(string_of_int(List.length stringlist))^"\n"^
          "je add_empty_list"^(string_of_int number1)^(string_of_int number) ^"\n\n"^

          "put_args_in_list"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^ 
          "mov r10,"^(string_of_int((List.length stringlist)))^"\n"^
          "sub r9,r10"^"\n"^
          "mov rcx,r9"^"\n"^
          "dec rcx"^"\n"^
          "mov r9,[rbp+3*8]"^"\n"^ (*[rbp+3*8] *)
          "add r9,3"^"\n"^
          "shl r9,3"^"\n"^
          "add r9,rbp"^"\n"^
          "mov r11, qword[r9]"^"\n"^
          "MAKE_PAIR(r15,r11,SOB_NIL)"^"\n"^
          "mov r12,r15"^"\n"^
          "sub r9, 8"^"\n"^
          "cmp rcx, 0"^"\n"^
          "je cont"^(string_of_int number1)^(string_of_int number)^"\n\n"^

          "loop"^(string_of_int number1)^(string_of_int number)^":"^"\n"^
          "mov r11, qword[r9]"^"\n"^
          "MAKE_PAIR(r15,r11,r12)"^"\n"^
          "mov r12,r15"^"\n"^
          "sub r9, 8"^"\n"^
          "loop loop"^(string_of_int number1)^(string_of_int number) ^", rcx"^"\n\n"^

          "cont"^(string_of_int number1)^(string_of_int number)^":\n"^

          "add r9, 8"^"\n"^
          "mov qword[r9],r12"^"\n"^
          "jmp continue"^(string_of_int number1)^(string_of_int number) ^"\n\n"^

          "add_empty_list"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          "mov qword[rbp+3*8],"^(string_of_int((List.length stringlist)+1))^"\n"^
          "sub rbp,8"^"\n"^
    
          "mov rcx,"^(string_of_int((List.length stringlist)+4))^"\n"^
          "mov r12,rbp"^"\n"^
          "add r12,8"^"\n\n"^

          "shift_down"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
          "mov r8,qword[r12]"^"\n"^
          "sub r12,8"^"\n"^
          "mov qword[r12],r8"^"\n"^
          "add r12,16"^"\n"^
          "loop shift_down"^(string_of_int number1)^(string_of_int number)^",rcx"^"\n\n"^

          "sub r12,8"^"\n"^
          "sub rsp,8"^"\n"^
          "mov r10, SOB_NIL "^"\n"^
          "mov qword[r12],r10"^"\n"^


          "continue"^(string_of_int number1)^(string_of_int number) ^":"^"\n"^
           

          (generate_helper consts fvars body number1 (depthOfLambda+1))^
          "leave\n"^
          "ret\n\n"^
          "Lcont"^(string_of_int number1)^(string_of_int number) ^":\n"


        )
    )
    | ApplicTP'(expr,exprlist)-> (
      let exprlist=(List.map (fun x->(generate_helper consts fvars x number1 depthOfLambda)^ "push rax\n") (List.rev exprlist)) in
        ((List.fold_left (fun x y-> x^y) "" exprlist)^
          
          "push "^(string_of_int((List.length exprlist)))^"\n"^
          (generate_helper consts fvars expr number1 depthOfLambda)^"\n"^ 
          "CLOSURE_ENV rcx ,rax\n"^
          "push rcx\n"^
          "push qword[rbp+8]"^"\n"^
          "mov r15,qword[rbp]"^"\n"^
          "SHIFT_FRAME("^(string_of_int((List.length exprlist)+3))^")\n"^ 
          "mov rbp,r15\n"^
          "CLOSURE_CODE rcx ,rax\n"^
          "jmp rcx\n"^ ""
        )
    )

    |_->"" 
  in generate_helper consts fvars e number1 depthOfLambda;;
  
end;;

