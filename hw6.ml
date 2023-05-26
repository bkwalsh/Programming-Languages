module SS = Set.Make(String)
module SMap = Map.Make(String)
module IMap = Map.Make(Int)

open List
open Char
open Format

exception Not_implemented
exception Parse_exn
exception NotAbs of string
exception NotFound of string
exception DuplicateVar of string
exception CaptureException of string (* maybe change*)

(* Data Definitions *)

type token
= LParen
| RParen
| TokLam
| TokDot
| TokVar of string
| TokIf 
| TokThen
| TokElse
| TokZero
| TokSucc
| TokPred
| TokIsZero
| TokColon
| TokBool
| TokNat
| TokArrow

type label = string

type typ 
= TUnit
| TRef of typ
| TBool
| TNat
| TFun of typ * typ
| TVariant of (label * typ) list 

type term
= TmVar of string
| TmAbs of string * typ * term
| TmApp of term * term
| TmUnit
| TmTrue 
| TmFalse 
| TmIf of term * term * term
| TmZero
| TmSucc of term
| TmPred of term
| TmIsZero of term
| TmVariant of label * term * typ (* eg. red = 6 as [red:Nat; blue:Nat] *)
| TmCase of term * (label * string * term) list (* eg. case red 2 of [red x => 5 | blue y => 9] *)
| TmRef of term 
| TmLoc of int 
| TmBang of term (* !t *)
| TmAssn of term * term 
| TmRaise of term
| TmTry of term * term
| TmNull
| TmIsNull of typ * term

(* Utilities *) 




let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* The tokenizer, lexer and parser are provided for you. *)

let rec nextToken (cs: char list) : (token * char list) option = 
  raise Not_implemented

let rec scan (ls : char list) : token list = raise Not_implemented

let rec nextTerm (ts: token list) : (term * token list) option = raise Not_implemented

let parse (tokens : token list) : term = raise Not_implemented

(* Helper functions*)

(* fresh_var helper, adds 'x' until strings don't match*)
let rec fresh_var_h (vars : SS.t)(build : string): string = 
  let build = build ^ (String.make 1 'x') in
  if (SS.mem build vars) then
    fresh_var_h (vars)(build)
  else
    build;;

(* takes a list of variable strings and produces a new string not in the set *)
let rec fresh_var (vars : SS.t): string = 
  fresh_var_h(vars)("");;

(* builds set given set, helper for fv*)
let rec fv_help (t:term)(set:SS.t): SS.t =
  match t with 
  | TmVar (c) ->  SS.add c set
  | TmAbs(s,ty,t) ->SS.remove s (fv_help(t)(set))
  | TmApp(t1,t2) -> SS.union (fv_help(t1)(set)) (fv_help(t2)(set))
  | _ -> raise Parse_exn;;

(* Get the free variables of t as a string set . *)
let rec fv (t:term) : SS.t =
  let set = SS.empty in 
  match t with 
  | TmVar (c) ->  SS.add c set
  | TmAbs(s,ty,t) ->SS.remove s (fv_help(t)(set))
  | TmApp(t1,t2) -> SS.union (fv_help(t1)(set)) (fv_help(t2)(set))
  | _ -> SS.empty;;

(* CaptureException of string*)
let rec subst (x : string) (s : term) (t : term) : term = 
  let set=fv(s) in
  match t with 
  | TmVar c -> if ((String.compare c x)==0) then s else  t
  | TmAbs(cc,ty,t1) -> if ((String.compare cc x)==0) then t else  if (SS.mem cc set) then
    raise (CaptureException "error") else TmAbs(cc,ty,subst x s t1)
  | TmApp(t2,t3) -> TmApp(subst x s t2,subst x s t3)
  | _ -> raise Parse_exn;;

(* given case term, do subtituion for the case and replace variables with the key
    return none if key can't be found*)
let rec casesub(search: term)(put:term)(key:string) : term option=
  match search with 
  | TmVar(s) -> if ((String.compare s key)==0) then Some(put) else Some(search)
  | TmAbs(s,ty,t1)-> if ((String.compare s key)==0) then Some(put) else Some(search)
  | TmApp(t1,t2)-> (match casesub t1 put key with
    | Some a->(match casesub t2 put key with
    | Some b-> Some(TmApp(a,b))
    | None->None) 
    | None->None)
  | TmIf(t1,t2,t3)-> (match casesub t1 put key with
  | Some a->(match casesub t2 put key with
  | Some b->(match casesub t3 put key with
  | Some c->Some(TmIf(a,b,c))
  | None->None)
  | None->None) 
  | None->None)
  | TmSucc(t1)->(match casesub t1 put key with
  | Some a->Some(TmSucc(a))
  | None->None)
  | TmPred(t1)->(match casesub t1 put key with
  | Some a->Some(TmPred(a))
  | None->None)
  | TmIsZero(t1) ->(match casesub t1 put key with
  | Some a->Some(TmIsZero(a))
  | None->None)
  | TmTrue -> Some(TmTrue) 
  | TmFalse -> Some(TmFalse)  
  | TmZero -> Some(TmZero) 
  | TmUnit -> Some(TmUnit) 
  | _ -> None;; 


(* Variants *)

(* Implement an option type, some and none as variants *)

(* considering using TUnit for tp of none, but going with logic from HW5
   that None has a tp assingment*)
let tp_opt (tp : typ) : typ =
  TVariant [  ("None", tp);  ("Some", tp)];;

let tm_some (t : term) (tp : typ) : term =
  TmVariant("Some",t,tp);;

let tm_none (tp : typ) : term =
  TmVariant("None",TmNull,tp);; 

(* Implement an exception type as a variant. 
   There are at least three possible exceptions that you should be able to handle. 
   (These should become clear as you progress through the homework, but feel free to start
    with some obvious candidates.) *)

let tp_exn : typ =   
  TVariant [  ("null_pointer_exception", TUnit); ("location_not_found", TUnit);  ("no_matching_case", TUnit)];;
 

(* Small-step evaluation *)

(* Implement the small-step evaluation relations from class. 
   Note the presence of a store and the possibility of encountering 
   raise and null. *)

type store = term IMap.t


(* helper function to grab a fresh key given a store*)
let rec fresh_key(mu:store)(key:int): int=
  match IMap.find_opt key mu with
    | Some (a)-> fresh_key(mu)(key+1) (* consider if this is step*)
    | None-> key;;

let rec handle_case(ol:label)(ot:term)(oty:typ)(tl:(label * string * term) list):(term) option=
  let compare_labels (label1 : label) (label2 : label) : int =
    String.compare label1 label2 in
  match tl with
  |[]-> None
  | x :: xs-> (match x with
    | (ll,s,lty)-> if (compare_labels ll ol==0) then 
      (match lty with 
      | TmVar(ss)-> if (String.compare  s ss==0) then Some(ot) else Some(lty)
      | _ -> Some (lty)
    ) else handle_case(ol:label)(ot:term)(oty:typ)(xs));;


let rec cbv (t : term) (mu : store) : (term*store) option =
  match t with
  | TmVar(s) -> None
  | TmTrue -> None 
  | TmFalse -> None 
  | TmZero -> None
  | TmUnit -> None
  | TmApp(TmNull,TmRaise(t1)) -> Some(TmRaise(t1),mu)
  | TmApp(TmNull,_) -> 
    Some(TmRaise((TmVariant("null_pointer_exception", TmUnit,tp_exn))),mu)
  | TmApp(TmAbs(s1,ty,ter1),TmRaise(t1)) -> Some(TmRaise(t1),mu)
  | TmApp(TmAbs(s1,ty,ter1),TmNull) -> Some(ter1,mu)
  | TmApp(TmRaise(t1),_) -> Some(TmRaise(t1),mu) 
  | TmApp(t1,TmRaise(t2)) -> (match cbv t1 mu with
    | None->Some(TmRaise(t1),mu)
    | Some(t3,mu2) -> Some(TmApp(t3,TmRaise(t2)),mu2))
  | TmApp(TmAbs(s1,ty,ter1),TmAbs(s2,ty2,ter2)) -> 
    Some(subst(s1)(ter2)(ter1),mu)
  | TmApp(TmAbs(s1,ty,ter),TmVar(s2)) -> Some(subst(s1)(TmVar(s2))(ter),mu)  
  | TmApp(TmAbs(s1,ty,ter),TmZero) -> (match casesub(ter)(TmZero)(s1) with
    |  Some a-> Some (a,mu)
    | _ -> None) 
  | TmApp(TmAbs(s1,ty,ter),TmUnit) -> (match casesub(ter)(TmUnit)(s1) with
  |  Some a-> Some (a,mu)
  | _ -> None)
  | TmApp(TmAbs(s1,ty,ter),TmTrue) -> (match casesub(ter)(TmTrue)(s1) with
  |  Some a-> Some (a,mu)
  | _ -> None) 
  | TmApp(TmAbs(s1,ty,ter),TmFalse) -> (match casesub(ter)(TmFalse)(s1) with
  |  Some a-> Some (a,mu)
  | _ -> None) 
  | TmApp(t1,t2) -> (match (cbv t1 mu) with
  | Some(a,store)->Some(TmApp(a,t2),store) 
  | _ -> (match (cbv t1 mu) with
  | Some (b,store)->Some(TmApp(t1,b),store) 
  | _ -> None))
  | TmAbs(s,ty,t1)-> (match cbv t1 mu with
    | None-> None
    | Some (a, store)->Some(TmAbs(s,ty,a),store))
  | TmSucc(t1)-> (match t1 with
  | TmPred(t2)-> Some (t2,mu)
  | _-> (match (cbv t1 mu) with 
  | Some(a,store)-> Some(TmSucc(a),store)
  | _ -> None))
  | TmPred(t1)-> (match t1 with
  | TmSucc(t2)-> Some (t2,mu)
  | _->  (match t1 with 
  | TmZero-> Some(TmZero,mu)
  | _ -> (match (cbv t1 mu) with 
  | Some(a,store)-> Some(TmPred(a),store)
  | _ -> None)))
  | TmIsZero(t1)->(match t1 with 
  | TmZero-> Some(TmTrue,mu)
  | _ -> match (cbv t1 mu) with 
    | Some(a,store)-> Some (TmIsZero(a),store)
    | None-> None)
  | TmIf(t1,t2,t3)-> (match t1 with
      | TmTrue-> Some(t2,mu)
      | TmFalse-> Some(t3,mu) 
      | a-> (match (cbv a mu) with
      | Some (b,store)->  Some(TmIf(b,t2,t3),store)
      | _-> None))
  | TmCase(t1,t2)->(
    match t1 with
    |TmVariant(l,ter,ty)-> (match t2 with 
    | [] -> Some(TmRaise(TmVariant("no_matching_case", TmUnit,tp_exn)),mu)
    | (ll, s, lty) :: xs -> (match handle_case l ter ty t2 with
    | Some(a)-> Some(a,mu) 
    | None-> None))
    |_ -> (match cbv t1 mu with
    |Some(ter1,mu2)->Some(TmCase(ter1,t2),mu2)
    |None-> None))
  | TmRef(t)-> (match cbv t mu with 
    | Some (a,mu2)-> Some(TmRef(a),mu2)
    | None ->  (let i=fresh_key(mu)(0) in
    let new_mu=IMap.add i t mu in 
    Some(TmLoc(i),new_mu)))
  | TmVariant(a,b,c)-> (match cbv b mu with 
    | Some(d,mu2)-> Some(TmVariant(a,d,c),mu2)
    | None-> None)
  | TmBang(t)-> (match t with
  | TmLoc(i)-> (match IMap.find_opt i mu with
  | Some (a)-> Some(a,mu) 
  | None-> Some(TmRaise(TmVariant("location_not_found", TmUnit,tp_exn)),mu))
  | t1-> (match cbv t1 mu with
    | Some(t2,mu2)-> Some(TmBang(t2),mu2)
    | None-> None))
  | TmLoc(i)-> (match IMap.find_opt i mu with
    | Some (a)-> Some(a,mu) 
    | None-> Some(TmRaise(TmVariant("location_not_found", TmUnit,tp_exn)),mu))
  | TmRaise(t1)-> (match cbv t1 mu with 
    | Some(a,b)-> Some(TmRaise(a),b)
    | None-> None)
  | TmAssn(t1,t2)->(match t1 with
  | TmLoc(i)-> (
    let new_mu=IMap.add i t2 mu in 
    Some(TmUnit,new_mu))
  | _-> None )
  | TmIsNull(ty,ter)-> (match ter with
    | TmNull-> Some(TmTrue,mu)
    | _-> (match cbv ter mu with
      | Some (a,mu2)-> Some(TmIsNull(ty,a),mu2)
      | _ -> Some(TmFalse,mu)))
  | TmTry(t1,t2)-> (match t1 with
    | TmRaise(t3)-> Some(TmApp(t2, t3),mu) 
    | TmNull-> Some(t1,mu)
    | _ -> (match cbv t1 mu with
      | None-> Some(t1,mu)
      | Some(a,mu2)->Some(TmTry(a,t2),mu2)))
  | _ -> None;; 



let rec multistep (t : term) : term =
  let startStore=IMap.empty in
  let rec multistep_drive(t1:term)(mu : store):term= 
    match cbv t1 mu  with 
    | Some(ter,store)-> multistep_drive(ter)(store)
    | None-> t in
    multistep_drive(t)(startStore);;


(* Typechecking utilities *)

type ctx = typ SMap.t
type typ_store = typ IMap.t 

let empty_ctx : ctx = SMap.empty

let empty_store : typ_store = IMap.empty

(* look up a given variable's typ, throw a NotFound exception if the variable is not found *)
let lookup (g : ctx) (x : string) : typ = match SMap.find_opt x g with
| Some t -> t
| None -> raise (NotFound x)

(* extend a context with a new variable-typ association *)
let extend (g : ctx) (x : string) (t : typ): ctx = 
  if SMap.mem x g then raise (DuplicateVar x)
  else SMap.add x t g


(* Helper functions*)  
(* checks for type equivilance, based on nested types*)
let rec type_eqv(t1:typ)(t2:typ) : bool=
  match t1 with 
  | TFun(p1,p2) ->(match t2 with
  | TFun(p3,p4) -> type_eqv(p1)(p3) && type_eqv(p2)(p4)
  | _ -> false)
  | a -> a==t2;;

(* check list to see if label and type correspond, returns bool*)  
let rec check_list(l: label)(l_t: typ)(ll:(label * typ) list): bool=
  match ll with
  | frst:: tail -> (match frst with 
  (lab,ty)-> if ((String.compare l lab)==0) && type_eqv l_t ty then true 
  else check_list(l: label)(l_t: typ)(tail))
  | _-> false ;; 

let rec null_stepper(t: term): bool=
  match t with
  | TmNull -> true
  | TmRaise(t1)-> true
  | _ -> false

(* check list to see if label and type correspond, returns typ*)    
let rec check_list_type_check(l: label)(ll:(label * typ) list): typ option=
match ll with
| frst:: tail -> (match frst with 
(lab,ty)-> if ((String.compare l lab)==0) then Some(ty) 
else check_list_type_check(l: label)(tail))
| _-> None ;; 


(* Typechecking *)

(* check if a term has the given type. *)
(* Takes in a context and a store, as well as a term t and type T *)
(* Returns true iff gamma | sigma |- t : T *)

let rec type_check (g : ctx) (s : typ_store) (t : term) (tp : typ) : bool =
  let rec find_match_case(ol:label)(ter:term)(tl:(label * typ) list):bool=
  let compare_labels (label1 : label) (label2 : label) : int =
    String.compare label1 label2 in
    match tl with
    |[]-> false
    | x :: xs-> (match x with
      | (ll,lty)-> if (compare_labels ll ol==0) then 
        type_check(g)(s)(ter)(lty) else find_match_case(ol)(ter)(xs)) in
  match t with
      | TmVar(s) ->true 
      | TmTrue -> tp==TBool
      | TmFalse-> tp==TBool
      | TmZero -> tp==TNat
      | TmUnit -> true
      | TmNull -> true
      | TmRaise(t1)-> false
      | TmRef(t1) -> (match tp with 
      |TRef(tyy)-> type_check g s t1 tyy
      | _-> false)
      | TmApp(TmAbs(str,typ1,t1),TmRaise(t2)) -> false 
      | TmIf(t1,t2,t3)-> if (type_check g s t1 TBool) 
        then (type_check g s t2 tp) && (type_check g s t3 tp) else false
      | TmApp(TmAbs(str,typ1,t1),t2)-> 
        if null_stepper t2 then type_check g s t1 tp
      else type_check g s t1 tp && type_check g s t2 typ1
      | TmApp(t1,t2) -> if null_stepper(t1) then true else 
        (type_check g s t1 tp) && (type_check g s t2 tp) 
      | TmAbs(str,typ1,t1) ->type_check g s t1 tp
      | TmSucc(t1)-> type_check g s t1 tp && tp==TNat
      | TmPred(t1)-> type_check g s t1 tp  && tp==TNat
      | TmIsZero(t1)-> type_check g s t1 TNat
      | TmVariant(l,t1,ty1) -> (match ty1 with
        | TVariant(ll) -> (match check_list_type_check(l)(ll) with 
          | Some(a)-> type_check g s t1 a
          | None-> false)
        | _-> false)
      | TmCase(t1,tll) ->(
        match t1 with
        |TmVariant(l,ter,ty)-> (match ty with 
        | TVariant(tll)  -> find_match_case(l)(ter)(tll) 
        | _-> false)
        |_ -> false) 
      | TmLoc(i)-> (match (IMap.find_opt i s) with
      | Some a->type_eqv (a) (tp)
      | None-> true)
      | TmBang(t1)-> (match t1 with
        |TmLoc(i)-> (match (IMap.find_opt i s) with
          | Some a->type_eqv (a) (tp)
          | None-> true) 
        | _ -> false)
      | TmAssn(t1,t2)-> if null_stepper t1 then true else 
        (match t1 with
        |TmLoc(i)-> (match (IMap.find_opt i s) with
          | Some a->type_eqv (a) (tp)
          | None-> false)
        | _ -> false)
      | TmTry(t1,t2) -> (match t2 with
          | TmAbs(_,tp_exn,ter)-> type_check g s ter tp
          | _ -> false )
      | TmIsNull(ty,t1)-> type_check g s t1 ty;;

  


(* This should infer the type of a term in the given context *)
(* return None if the term is ill-typed OR the type cannot be inferred *)
(* You may want to use type_check or other helper functions in writing this. *)
let rec type_infer (g : ctx) (s : typ_store) (t : term) : typ option =

  let rec find_match_case(ol:label)(ter:term)(tl:(label * typ) list):typ option=
    let compare_labels (label1 : label) (label2 : label) : int = 
    String.compare label1 label2 in
    match tl with
    |[]-> None
    | x :: xs-> (match x with
    | (ll,lty)-> if (compare_labels ll ol==0) then
       (match type_infer(g)(s)(ter) with
    |Some a-> if type_eqv a lty then Some a else None
    |_->None) else find_match_case(ol)(ter)(xs)) in


  match t with
      | TmVar(s) ->Some(lookup(g)(s))
      | TmTrue -> Some(TBool)
      | TmFalse-> Some(TBool)
      | TmZero -> Some(TNat)
      | TmUnit -> Some(TUnit)
      | TmNull -> None
      | TmRaise(t1)-> None
      | TmApp(TmAbs(str,typ1,t1),TmRaise(t2)) -> Some(typ1) 
      | TmApp(TmAbs(str,typ1,t1),TmNull) -> Some(typ1)  
      | TmApp(TmAbs(str,typ1,t1),t2)-> if null_stepper t2 then type_infer g s t1 
      else (match type_infer g s t2 with
      | Some(a) ->(match type_infer g s (TmAbs(str,typ1,t1)) with 
      |Some(TFun(b,c))-> if(a==b) then Some(c) else None
      | _->None)
      | None-> None)   
      | TmAbs(str,typ1,t1) ->(
      let g_1= extend g str typ1 in 
      match type_infer g_1 s t1 with
          |Some (a) -> Some(TFun(typ1,a))
          |None -> None) 
      | TmApp(t1,t2) -> (match type_infer g s t2 with
        | Some(a) ->(match type_infer g s t1 with 
        |Some(TFun(b,c))-> if(a==b) then Some(c) else None
        | _->None)
        | None-> None)
      | TmIf(t1,t2,t3)-> if null_stepper(t1) then 
        (if null_stepper(t2) then  type_infer g s t3 else 
          if null_stepper(t3) then  type_infer g s t2 else  
            (match type_infer g s t2 with
          | Some(ta1)-> (match type_infer g s t3 with
          | Some(ta2)-> if type_eqv(ta1)(ta2) then Some(ta1) else None
          | _ ->None) 
          | _ ->None) ) else
        (match type_infer g s t1 with
        |Some (TBool)->(if null_stepper(t2) then  type_infer g s t3 else 
          if null_stepper(t3) then  type_infer g s t2 else 
            (match type_infer g s t2 with
          | Some(ta1)-> (match type_infer g s t3 with
          | Some(ta2)-> if type_eqv(ta1)(ta2) then Some(ta1) else None
          | _ ->None) 
          | _ ->None))
        | _-> None)
      | TmSucc(t1)-> (match type_infer g s t1 with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmPred(t1)-> (match type_infer g s t1 with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmIsZero(t1)-> (match type_infer g s t1 with
          |Some (TNat) ->  Some(TBool)
          |Some (TFun(a,TNat)) ->Some(TFun(a,TBool))
          |_ -> None)
      | TmVariant(l,t1,ty1) -> (match ty1 with
        | TVariant(ll) -> (match type_infer g s t1 with 
          | Some(a) -> if check_list(l)(a)(ll) then Some(ty1) else None
          | None-> None)
        | _-> None)
      | TmCase(t1,tll) ->(
        match t1 with
        |TmVariant(l,ter,ty)-> (match ty with 
        | TVariant(tll)  -> find_match_case(l)(ter)(tll) 
        | _-> None) 
        |_ -> type_infer g s t1)
      | TmRef(t1) -> (match type_infer g s t1 with
        |Some(a)-> Some(TRef(a))
        | None-> None)
      | TmLoc(i)-> IMap.find_opt i s
      | TmBang(t1)-> (match t1 with
        |TmLoc(i)->IMap.find_opt i s
        | _ -> None)
      | TmAssn(t1,t2)-> if null_stepper t1 then Some(TUnit) else 
        (match t1 with
        |TmLoc(i)-> (match IMap.find_opt i s with
        | Some a-> (match type_infer g s t2 with
          | Some b->if type_eqv a b then Some(TUnit) else None
          | None-> None)
        | None-> None)
        | _-> None
        )
      | TmTry(t1,t2) ->(match t2 with
          | TmAbs(_,tp_exn,ter)-> type_infer g s ter
          | _ -> None )
      | TmIsNull(ty,t1)->( match t1 with
        | TmNull-> Some(TBool) 
        | _-> (match type_infer g s t1 with
        | Some(a)-> if type_eqv a ty then Some(TBool) else None
        | None-> None ));;




(* Checks if the given store is well typed with respect to the given type_store
   and typing context. *)
(* Returns true iff gamma | sigma |- mu *)

(* helper function to search for a type in a ctx and remove it if it exists, 
   returning true and the updated ctx if it exists, and false with the old ctx 
    if it doesn't exist.*)
let zap_ctx_wrapper (g : ctx) (typsearch : typ) : ctx * bool =
  let rec zap_ctx (key : string) (acc : ctx) (updated : bool) : ctx * bool =
    if  updated then (acc, updated)
    else let g_val = lookup g key in
      if (type_eqv typsearch g_val) then (let g' = SMap.remove key acc in
        (g', true))
      else (acc, updated) in
  let (updated_ctx, updated) = SMap.fold (fun x ty (acc, updated) 
  -> zap_ctx x acc updated) g (g, false) in
  (updated_ctx,updated);;



let store_well_typed (g : ctx) (s : typ_store) (mu : store): bool =
  let rec check_well_typed (key : int) (acc : ctx)(updated : bool)(mu_mut:store): ctx * bool * store =
    if  (not updated) then (acc,false,mu_mut) else 
    let mu_opt = IMap.find_opt key mu in
    let s_opt = IMap.find_opt key s in
    (match mu_opt with
    | Some m_term-> (match s_opt with
    | Some s_ty->(match type_infer acc s m_term with
    | Some (m_ty)-> if type_eqv s_ty m_ty then (let new_ctx = 
      fst (zap_ctx_wrapper acc s_ty) in let new_mu = IMap.remove key mu_mut in
                      (new_ctx, true,new_mu)) else (acc,false,mu_mut)
      | None->(acc,false,mu_mut) )
      | None-> (acc,false,mu_mut))
    | None ->(match s_opt with
    | Some s_ty->  
      let removed = snd (zap_ctx_wrapper acc s_ty) in
      let new_ctx = fst (zap_ctx_wrapper acc s_ty) in
      if removed then (new_ctx,true,mu_mut) else (acc,false,mu_mut) 
    | _ -> (acc,false,mu_mut)))  in let (new_g, outcome,new_mu) = 
    IMap.fold (fun x ty (acc,updated,mu) -> 
      check_well_typed x acc updated mu) s (g,true,mu)  in
    outcome && (SMap.is_empty new_g) && (IMap.is_empty new_mu);;




(* Interpreter *)

(* This is for you to debug your code. *)
(* The current interpret function will parse a term and return its
  type in the empty context. *)
(* You're encouraged to add additional tests. *)

let rec typ_to_string (t : typ) : string = match t with
| TBool -> "Bool"
| TNat -> "Nat"
| TFun(t1,t2) -> "(" ^ typ_to_string t1 ^ "->" ^ typ_to_string t2 ^ ")"

let rec term_to_string (t : term) : string = match t with
| TmVar(str) -> str
| TmAbs(var, tp, body) -> "&" ^ var ^ ":" ^ typ_to_string tp ^ "." ^ term_to_string body
| TmApp(t1, t2) -> "(" ^ term_to_string t1 ^ ") (" ^ term_to_string t2 ^ ")"
| TmTrue -> "True"
| TmFalse -> "False"
| TmZero -> "0"
| TmIf (t1, t2, t3) -> "If " ^ term_to_string t1 ^ " Then " ^ term_to_string t2 ^ " Else " ^ term_to_string t3
| TmSucc (t1) -> "Succ " ^ term_to_string t1
| TmPred (t1) -> "Pred " ^ term_to_string t1
| TmIsZero (t1) -> "IsZero " ^ term_to_string t1

let opt_typ_to_string (o : typ option) : string = 
  match o with
  | None -> " "
  | Some t -> typ_to_string t 

  let interpret (str : string) : unit =
    let chars = string_to_char_list str in
    let tokens = scan chars in
    let ast = parse tokens in
    let term_str = term_to_string ast in
    let _ = print_endline ("----- Type Inference -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline (": " ^ (opt_typ_to_string (type_infer empty_ctx empty_store ast))) in
    print_endline "";;


interpret Sys.argv.(1)