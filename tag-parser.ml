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
