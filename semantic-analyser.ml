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
(* Semantics.run_semantics(Tag_Parser.tag_parse_expression(Reader.read_sexpr("
(if #f 3) 
"))) *)