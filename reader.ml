
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
   | Vector(l1), Vector(l2) -> if(List.length l1 !=List.length l2)then false else ( List.for_all2 sexpr_eq l1 l2)
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
 
 nt_SexprComment s = (pack (caten (char '#') (caten (char ';') (caten nt_Sexpr (nt_Sexpr))))
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

