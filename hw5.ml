module SS = Set.Make(String)

open List
open Char
open Format

exception Not_implemented
exception Parse_exn
exception NotAbs of string
exception NotFound of string
exception DuplicateVar of string
exception CaptureException of string
exception BadInput (* CONSIDER IF I NEED added to handle tm_opt_case, explained there*)

(* Data Definitions *)

type token
= LParen
| RParen
| LCurly
| RCurly
| LSquare
| RSquare
| TokLam
| TokDot
| TokVar of string
| TokIf 
| TokThen
| TokFst
| TokSnd
| TokElse
| TokZero
| TokSucc
| TokPred
| TokIsZero
| TokColon
| TokBool
| TokTrue
| TokFalse
| TokOf
| TokNat
| TokArrow
| TokFatArrow
| TokCross
| TokPlus
| TokWith
| TokNil
| TokCons
| TokIsNil
| TokHead
| TokUnit
| TokTail
| TokBar
| TokCase
| TokComma
| TokInl
| TokInr

type typ 
= TUnit
| TBool
| TNat 
| TFun of typ * typ
| TProd of typ * typ 
| TSum of typ * typ
| TList of typ

type term
= TmVar of string
| TmAbs of string * typ * term
| TmApp of term * term
| TmTrue 
| TmFalse 
| TmZero
| TmIf of term * term * term
| TmSucc of term
| TmPred of term
| TmIsZero of term
| TmUnit
| TmPair of term * term
| TmFst of term
| TmSnd of term
| TmInl of typ * term
| TmInr of typ * term
| TmCase of term * string * term * string * term (* case term1 of inl string1 => term2 | inr string2 => term3 *)
| TmNil of typ
| TmCons of typ * term * term 
| TmIsNil of typ * term 
| TmHead of typ * term 
| TmTail of typ * term 

(* Utilities *) 

let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* The tokenizer, lexer and parser are provided for you. *)

let varStart (c : char) : bool = 
  match c with
  | 'a'..'z' -> true
  | _ -> false

let validVar (c: char) : bool = 
  match c with
  | 'a'..'z' -> true
  | 'A'..'Z' -> true
  | '0'..'9' -> true
  | _ -> false

let rec nextVar (cs: char list) : (char list * char list) =
  match cs with
  | [] -> ([], [])
  | c::tl -> 
    if validVar c 
    then (match nextVar tl with
      | (var, rem) -> (c::var, rem))
    else ([], c::tl)

let rec nextToken (cs: char list) : (token * char list) option = 
  match cs with
  | '0'::tl -> Some (TokZero, tl)
  | 'X'::tl -> Some(TokCross, tl)
  | '+'::tl -> Some(TokPlus, tl)
  | 'o'::'f'::tl -> Some(TokOf, tl)
  | 'u'::'n'::'i'::'t'::tl -> Some (TokUnit, tl)
  | 'c'::'a'::'s'::'e'::tl -> Some(TokCase, tl)
  | 'S'::'u'::'c'::'c'::tl -> Some (TokSucc, tl)
  | 'P'::'r'::'e'::'d'::tl -> Some (TokPred, tl)
  | 'T'::'r'::'u'::'e'::tl -> Some (TokTrue, tl)
  | 'F'::'a'::'l'::'s'::'e'::tl -> Some (TokFalse, tl)
  | 'I'::'f'::tl -> Some (TokIf, tl)
  | 'T'::'h'::'e'::'n'::tl -> Some (TokThen, tl)
  | 'E'::'l'::'s'::'e'::tl -> Some (TokElse, tl)
  | 'I'::'s'::'Z'::'e'::'r'::'o'::tl -> Some (TokIsZero, tl)
  | 'B'::'o'::'o'::'l'::tl -> Some (TokBool, tl)
  | 'N'::'a'::'t'::tl -> Some (TokNat, tl)
  | 'n'::'i'::'l'::tl -> Some (TokNil, tl)
  | 'c'::'o'::'n'::'s'::tl -> Some(TokCons, tl)
  | 'w'::'i'::'t'::'h'::tl -> Some(TokWith, tl)
  | 'i'::'s'::'n'::'i'::'l':: tl -> Some(TokIsNil, tl)
  | 'h'::'e'::'a'::'d'::tl -> Some (TokHead, tl)
  | 't'::'a'::'i'::'l'::tl -> Some(TokTail, tl)
  | 'f'::'s'::'t'::tl -> Some(TokFst, tl)
  | 's'::'n'::'d'::tl -> Some(TokSnd, tl)
  | 'i'::'n'::'l'::tl -> Some (TokInl, tl)
  | 'i'::'n'::'r'::tl -> Some (TokInr, tl)
  | '-'::'>'::tl -> Some (TokArrow, tl)
  | '='::'>'::tl -> Some (TokFatArrow, tl)
  | ':'::tl -> Some(TokColon, tl)
  | '('::tl -> Some(LParen, tl)
  | '{'::tl -> Some(LCurly, tl)
  | '['::tl -> Some(LSquare, tl)
  | ']'::tl -> Some(RSquare, tl)
  | '}'::tl -> Some(RCurly, tl)
  | ')'::tl -> Some(RParen, tl)
  | '|'::tl -> Some(TokBar, tl)
  | '&'::tl -> Some(TokLam, tl)
  | '.'::tl -> Some(TokDot, tl)
  | ','::tl -> Some(TokComma, tl)
  | ' '::tl -> nextToken tl
  | c::tl -> 
    (if (varStart c)
      then (match nextVar (c::tl) with
            | (var, rem) -> Some (TokVar (char_list_to_string var), rem))
      else (raise Parse_exn))
  | [] -> None


let rec scan (ls : char list) : token list =
  match nextToken ls with
    | Some (tok, tl) -> tok :: scan tl
    | None -> []

let rec nextType (ts : token list) : (typ * token list) option =
  match ts with
  | TokNat::tl -> Some(TNat, tl)
  | TokBool::tl -> Some(TBool, tl)
  | TokUnit::tl -> Some(TUnit, tl)
  | LParen::tl -> (match tl with
    | TokCross::tl' -> (match nextType tl' with
      | Some(ty0, tl'') -> (match nextType tl'' with
        | Some(ty1, tl''') -> Some(TProd(ty0, ty1), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | TokPlus::tl' -> (match nextType tl' with
      | Some(ty0, tl'') -> (match nextType tl'' with
        | Some(ty1, tl''') -> Some(TSum(ty0, ty1), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | TokArrow::tl' -> (match nextType tl' with
      | Some(ty0, tl'') -> (match nextType tl'' with
        | Some(ty1, tl''') -> Some(TFun(ty0, ty1), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | LSquare::tl -> (match nextType tl with
    | Some(ty0, RSquare::tl') -> Some(TList(ty0), tl')
    | _ -> raise Parse_exn)
  | _ -> raise Parse_exn    

let rec nextTerm (ts: token list) : (term * token list) option = 
  match ts with
  | TokVar(var)::tks -> Some(TmVar(var), tks)
  | LParen::tks ->(match nextTerm tks with
    | Some (tm0, RParen::LParen::tks') -> (match nextTerm tks' with
      | Some (tm1, RParen::tks'') -> Some(TmApp(tm0, tm1), tks'')
      | _ -> raise Parse_exn)
    | Some (tm1, TokComma::tks'') ->( match nextTerm tks'' with
      | Some(tm2, RParen::tks''') -> Some(TmPair(tm1, tm2), tks''')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokLam::TokVar(var)::TokColon::tl -> (match nextType tl with 
    | Some(ty0, TokDot::tl') -> (match nextTerm tl' with
      | Some(tm0, tl'') -> Some(TmAbs(var, ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokTrue::tl -> Some (TmTrue, tl)
  | TokFalse::tl -> Some (TmFalse, tl)
  | TokIf::tl -> (match nextTerm tl with
    | Some(tm0, TokThen::tl') -> (match nextTerm tl' with
      | Some(tm1, TokElse::tl'') -> (match nextTerm tl'' with
        | Some(tm2, tl''') -> Some(TmIf(tm0, tm1, tm2), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokZero::tl -> Some (TmZero, tl)
  | TokIsZero::tl -> 
    (match nextTerm tl with
    | Some (trm, tl0) -> Some (TmIsZero trm, tl0)
    | _ -> raise Parse_exn)
  | TokPred::tl ->
    (match nextTerm tl with
    | Some (trm, tl0) -> Some (TmPred trm, tl0)
    | _ -> raise Parse_exn)
  | TokSucc::tl ->
    (match nextTerm tl with
    | Some (trm, tl0) -> Some (TmSucc trm, tl0)
    | _ -> raise Parse_exn)
  | LCurly::tks -> (match nextTerm tks with
    | Some (tm0, TokComma::tks') -> (match nextTerm tks' with
      | Some (tm1, RCurly::tks'') -> Some(TmPair(tm0, tm1), tks'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokUnit::tl -> Some(TmUnit, tl)
  | TokFst::tks -> (match nextTerm tks with
    | Some (tm0, tks') -> Some(TmFst(tm0), tks')
    | _ -> raise Parse_exn)
  | TokSnd::tks -> (match nextTerm tks with
    | Some (tm0, tks') -> Some(TmSnd(tm0), tks')
    | _ -> raise Parse_exn)
  | TokHead::tl -> (match nextType tl with
    | Some(TList(ty0), tl') -> (match nextTerm tl' with
      | Some(tm0, tl'') -> Some(TmHead(ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokTail::tl -> (match nextType tl with
    | Some(TList(ty0), tl') -> (match nextTerm tl' with
      | Some(tm0, tl'') -> Some(TmTail(ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokNil::tl -> (match nextType tl with
    | Some(TList(ty0), tl') -> Some(TmNil(ty0), tl')
    | _ -> raise Parse_exn)
  | TokCons::tl -> (match nextType tl with
    | Some(TList(ty0), tl') -> (match nextTerm tl' with
      | Some(tm0, tl'') -> (match nextTerm tl'' with
        | Some(tm1, tl''') -> Some(TmCons(ty0, tm0, tm1), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokIsNil::tl -> (match nextType tl with
    | Some(TList(ty0), tl') -> (match nextTerm tl' with
      | Some(tm0, tl'') -> Some(TmIsNil(ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokInl::tl -> (match nextTerm tl with
    | Some(tm0, TokWith::tl') -> (match nextType tl' with
      | Some(ty0, tl'') -> Some(TmInl(ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokInr::tl -> (match nextTerm tl with
    | Some(tm0, TokWith::tl') -> (match nextType tl' with
      | Some(ty0, tl'') -> Some(TmInr(ty0, tm0), tl'')
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | TokCase::tl -> (match nextTerm tl with
    | Some(tm0, TokOf::TokInl::TokVar(x1)::TokFatArrow::tl') -> (match nextTerm tl' with
      | Some(tm1, TokBar::TokInr::TokVar(x2)::TokFatArrow::tl'') -> (match nextTerm tl'' with
        | Some(tm2, tl''') -> Some(TmCase(tm0, x1, tm1, x2, tm2), tl''')
        | _ -> raise Parse_exn)
      | _ -> raise Parse_exn)
    | _ -> raise Parse_exn)
  | _ -> raise Parse_exn

let parse (tokens : token list) : term = 
  match nextTerm tokens with
  | Some (trm, []) -> trm
  | _ -> raise Parse_exn



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
  | TmPair(t1,t2)-> (match casesub t1 put key with
    | Some a->(match casesub t2 put key with
    | Some b-> Some(TmPair(a,b))
    | None->None) 
    | None->None)
  | TmFst(t1)->(match casesub t1 put key with
  | Some a->Some(TmSucc(a))
  | None->None)
  | TmSnd(t1)->(match casesub t1 put key with
  | Some a->Some(TmSucc(a))
  | None->None)
  | TmIsNil(ty,t1)->(match casesub t1 put key with
  | Some a->Some(TmIsNil(ty,a))
  | None->None)
  | TmHead(ty,t1)->(match casesub t1 put key with
  | Some a->Some(TmIsNil(ty,a))
  | None->None)
  | TmTail(ty,t1)->(match casesub t1 put key with
  | Some a->Some(TmIsNil(ty,a))
  | None->None)
  | TmCons(ty1,t1,t2)-> (match casesub t1 put key with
    | Some a->(match casesub t2 put key with
    | Some b-> Some(TmCons(ty1,a,b))
    | None->None) 
    | None->None)
  | TmNil(ty)-> Some(TmNil(ty))
  | TmTrue -> Some(TmTrue) 
  | TmFalse -> Some(TmFalse)  
  | TmZero -> Some(TmZero) 
  | TmUnit -> Some(TmUnit) 
  | _ -> None;; 

(* Implement the derived forms t;t, let x : T = t in t, option T
   and option case from the book and class. *)
(* In t;t, the first t should have type unit. *)
(* In let, note that x is annotated with a type.  *)
(* option T use a sum type to encode an option type *)
(* option case should case on None and Some t, returning a term for each case *)

let rec tm_seq (t1 : term) (t2 : term) : term =
  TmApp(TmAbs(fresh_var(fv(t2)),TUnit,t2),t1);;


let tm_let (x : string) (tp : typ) (t1 : term) (t2 : term) : term =
  TmApp(TmAbs(x,tp,t2), t1);;

let tp_opt (tp : typ) : typ =
  TSum(TUnit,tp);;

let tm_some (t :term) : term =
  TmPair(TmUnit,t);;

let tm_none (t : typ) : term = 
  TmPair(TmUnit,TmNil(t));;

let tm_opt_case (t: term) (t_some : string -> term) (t_none : term) : term = 
  let var=fresh_var(fv(t)) in
  match t with
  | TmPair(TmUnit,TmNil(t1))-> t_none
  | TmPair(TmUnit,t1) -> (match casesub(t_some(var))(t1)(var) with
    | Some a-> a
    | _ -> raise (NotFound var))
  | _ -> raise BadInput;; (* not fiven Some or Type Unit in term, so error*)
  

(* Small-step evaluation *)

(* Implement the small-step evaluation relations from class. 
   Note that we're only concerned with call-by-value for this homework. 
   Feel free to reuse code from homework 3. 
   (Implementing capture-avoiding substitution is encouraged, but not what we 
   will be grading this on) *)

(* helper for cbv, does all the heavy lifting but doesn't consdier stuck terms*)
let rec cbv_w (t : term) : term option =
  match t with
  | TmVar(s) -> None
  | TmTrue -> None 
  | TmFalse -> None 
  | TmZero -> None
  | TmUnit -> None
  | TmNil(ty)-> None
  | TmCons(ty,t1,t2)-> (match cbv_w t1 with
    | Some(a)-> Some(TmCons(ty,a,t2))
    | _ -> (match cbv_w t2 with
      | Some(b)->Some(TmCons(ty,t1,b)) 
      | _-> None))
  | TmApp(TmAbs(s1,ty,ter1),TmAbs(s2,ty2,ter2)) -> Some(subst(s1)(ter2)(ter1))
  | TmApp(TmAbs(s1,ty,ter),TmVar(s2)) -> Some(subst(s1)(TmVar(s2))(ter))
  | TmApp(TmAbs(s1,ty,ter),TmZero) -> casesub(ter)(TmZero)(s1)
  | TmApp(TmAbs(s1,ty,ter),TmUnit) -> casesub(ter)(TmUnit)(s1)
  | TmApp(TmAbs(s1,ty,ter),TmTrue) -> casesub(ter)(TmTrue)(s1)
  | TmApp(TmAbs(s1,ty,ter),TmFalse) -> casesub(ter)(TmFalse)(s1)
  | TmApp(TmAbs(s1,ty,ter),TmNil(ty1)) -> casesub(ter)(TmNil(ty1))(s1)
  | TmApp(t1,t2) -> (match (cbv_w t1) with
  | Some a->Some(TmApp(a,t2)) 
  | _ -> (match (cbv_w t2) with
  | Some b->Some(TmApp(t1,b)) 
  | _ -> None))
  | TmAbs(s,ty,t1)-> (match cbv_w t1 with
    | None-> None
    | Some a->Some(TmAbs(s,ty,a)))
  | TmSucc(t1)-> (match t1 with
  | TmPred(t2)-> Some (t2)
  | _-> (match cbv_w t1 with 
  | Some(a)-> Some(TmSucc(a))
  | _ -> None))
  | TmPred(t1)-> (match t1 with
  | TmSucc(t2)-> Some (t2)
  | _->  (match t1 with 
  | TmZero-> Some(TmZero)
  | _ -> (match cbv_w t1 with 
  | Some(a)-> Some(TmPred(a))
  | _ -> None)))
  | TmIsZero(t1)->(match t1 with 
  | TmZero-> Some(TmTrue)
  | _ -> match cbv_w t1 with 
    | Some(a)-> Some (TmIsZero(a))
    | None-> None)
  | TmFst(TmPair(x,y))-> (match cbv_w x with
  | None-> Some x
  | Some a->Some(TmFst(TmPair(a,y))))
  | TmSnd(TmPair(x,y))-> (match cbv_w y with
  | None-> Some y
  | Some a->Some(TmSnd(TmPair(x,a))))
  | TmInr(ty,ter1)-> (match cbv_w ter1 with
    | Some a-> Some(TmInr(ty,a))
    | _-> None) 
  | TmInl(ty,ter1)-> (match cbv_w ter1 with
    | Some a-> Some(TmInl(ty,a))
    | _-> None) 
  | TmPair(t1,t2) ->(match (cbv_w t1) with
  | Some a->Some(TmPair(a,t2)) 
  | _ -> (match (cbv_w t2) with
  | Some b->Some(TmPair(t1,b)) 
  | _ -> None)) 
  | TmIf(t1,t2,t3)-> (match t1 with
      | TmTrue-> Some(t2)
      | TmFalse-> Some(t3) 
      | a-> (match cbv_w a with
      | Some b->  Some(TmIf(b,t2,t3))
      | _-> None))
  | TmHead(ty,t1) -> (match t1 with
  | TmCons(ty2,t2,t3) -> Some (TmInr (TUnit, t2))
  | TmNil(a)->  Some (TmInl (a, TmUnit))
  | _ -> None) 
  | TmTail(ty,t1) -> (match t1 with 
  | TmNil(a)-> Some (TmNil a)
  | TmCons(ty,a,TmNil(b))-> Some (TmNil b)
  | TmCons(ty,a,c)-> Some (c)
  | _ -> None)
  | TmIsNil(ty,trm) ->(match trm with
  | TmNil(ty2)-> Some(TmTrue)
  |_ -> (match cbv_w trm with
    | Some(a) ->Some(TmIsNil(ty,a))
    | _-> Some(TmFalse)))
  | TmCase(t1,s1,t2,s2,t3)->(match t1 with
  | TmInr(typ1,t4)-> (match (cbv_w t4) with
  | Some(b)->Some(TmCase(TmInr(typ1,b) ,s1,t2,s2,t3))
    | _ -> casesub(t3)(t4)(s2))
  | TmInl(typ1,t4)-> (match (cbv_w t4) with
 | Some(a)-> Some(TmCase(TmInl(typ1,a) ,s1,t2,s2,t3))
 |_  -> casesub(t2)(t4)(s1))
  | _ -> None)
  | _ -> None;;  


  let rec stuck(t:term): bool=
  match t with
  | TmIf(t1,t2,t3) ->(match  t1  with
  | TmVar(s) -> true
  | TmZero -> true
  | TmUnit -> true
  | TmNil(ty)-> true
  | _-> false) 
  | TmSucc(t1) ->(match  t1  with
  | TmVar(s) -> true
  | TmUnit -> true
  | TmNil(ty)-> true
  | TmTrue -> true 
  | TmFalse -> true 
  | _-> false) 
  | TmPred(t1) ->(match  t1  with
  | TmVar(s) -> true
  | TmUnit -> true
  | TmNil(ty)-> true
  | TmTrue -> true 
  | TmFalse -> true 
  | _-> false) 
  | TmIsZero(t1) ->(match  t1  with
  | TmVar(s) -> true
  | TmUnit -> true
  | TmNil(ty)-> true
  | TmTrue -> true 
  | TmFalse -> true 
  | _-> false)
  | TmVar(s) -> false
  | TmTrue -> false 
  | TmFalse -> false 
  | TmZero -> false
  | TmUnit -> false
  | TmNil(ty)-> false
  | TmCons(ty,t1,t2)-> if stuck t1 then true else (if cbv_w t1!= None then false else stuck t2)
  | TmApp(TmAbs(s1,ty,ter),TmVar(s2)) -> false
  | TmApp(TmAbs(s1,ty,ter),TmZero) -> false
  | TmApp(TmAbs(s1,ty,ter),TmUnit) -> false
  | TmApp(t1,t2) -> if stuck t1 then true else (if cbv_w t1!= None then false else stuck t2)
  | TmAbs(s,ty,t1)-> stuck t1
  | TmFst(TmPair(x,y))-> stuck x
  | TmSnd(TmPair(x,y))-> stuck y
  | TmInr(ty,ter1)-> stuck ter1
  | TmInl(ty,ter1)-> stuck ter1 
  | TmPair(t1,t2) ->if stuck t1 then true else (if cbv_w t1!= None then false else stuck t2)
  | TmHead(ty,t1) -> stuck t1
  | TmTail(ty,t1) -> stuck t1
  | TmIsNil(ty,trm) ->false
  | TmCase(t1,s1,t2,s2,t3)->(match t1 with
  | TmInr(typ1,t4)-> stuck t4
  | TmInl(typ1,t4)-> stuck t4
  | _ -> false)
  |_-> false ;;



(* for cbv, used simple wrapper with cbv_w. uses stuck to see if 
   term is stuck before it steps*)
let cbv(t: term): term option =
  if stuck(t) then None else cbv_w(t);;



let rec multistep (t : term) : term option =
  match cbv t with 
  | Some(a) -> cbv a 
  | None-> Some t;;


(* Typechecking utilities *)

(* These first few functions can be copied from prior homeworks. 
   We will try to give solutions shortly after the late deadline. *)

(* give a reasonable type to context *)
type ctx
= Empty_ctx
| Gam of string * typ * ctx

(* define the empty context *)
let empty_ctx : ctx = Empty_ctx;;

(* look up a given variable's typ, throw a NotFound exception if the variable is not found *)
let rec lookup (g : ctx) (x : string) : typ =
  match g with
  | Empty_ctx -> raise (NotFound x)
  | Gam(s,ty,prev) -> if ((String.compare s x)==0) 
    then ty else lookup (prev) (x);;

(* extend a context with a new variable-typ association *)
let rec extend (g : ctx) (x : string) (t : typ): ctx =
  (* replace empty ctxx*)
  let rec recur_down(g: ctx): ctx=
    match g with
    | Empty_ctx -> Gam(x,t,Empty_ctx)
    | Gam(xp,tp,Empty_ctx) -> Gam(xp,tp,Gam(x,t,Empty_ctx))
    | Gam(xpp,tpp,c) -> Gam(xpp,tpp,recur_down(c)) in

  (* check duplicates*)
  let rec noduplicate (g : ctx): bool =
    match g with
    | Empty_ctx -> true
    | Gam(s,ty,prev) -> if ((String.compare s x)==0) 
      then false else noduplicate (prev) in
  if (noduplicate(g)) then recur_down(g)  else raise (DuplicateVar x);;


(* Typechecking *)

(* return the type of a term in the given context *)
(* return None if the term is ill-typed *)
  
let rec type_of (g : ctx) (t : term) : typ option = 

  (* checks for type equivilance, based on nested types*)
  let rec type_eqv(t1:typ)(t2:typ) : bool=
    match t1 with 
    | TFun(p1,p2) ->(match t2 with
    | TFun(p3,p4) -> type_eqv(p1)(p3) &&  type_eqv(p2)(p4)
    | _ -> false)
    | a -> a==t2 in

  (* returns type if string can be found- essentially lookup but to return 
     None instead of error*)
  let rec find_type(gg:ctx)(svar:string) : typ option=
    match gg with
    | Empty_ctx -> None
    | Gam(s,ty,prev) -> if ((String.compare s svar)==0) 
      then Some (ty) else find_type(prev)(svar) in   
    
 (* given list and type, make sure type is consistnet and list ends with 
    nil impliment checking list consistency function*)
    let rec list_consistency(t1: term)(cons_tp:typ): bool=
    match t1 with
    | TmCons(typ2, t2,t3) -> if typ2==cons_tp then list_consistency(t3)(cons_tp)
      else false
    | TmNil(typ2)-> if typ2==cons_tp then true
    else false
    | _ -> false in

  match t with
      | TmVar(s) ->find_type(g)(s)
      | TmTrue -> Some(TBool)
      | TmFalse-> Some(TBool)
      | TmZero -> Some(TNat)
      | TmUnit -> Some(TUnit)
      | TmNil(t1)->Some (TList t1)
      | TmInl(ty1,ter1) -> (match type_of (g)(ter1) with
      | Some(a) -> Some(TSum(a,ty1)) 
      | _-> None)
      | TmInr(ty1,ter1) -> (match type_of (g)(ter1) with
      | Some(a) ->Some(TSum(ty1,a)) 
      | _-> None )
      | TmPair(t1,t2) -> (match type_of (g)(t1) with
      | Some(a) ->(match type_of (g)(t2) with 
      |Some(b)-> Some(TProd(a,b))
      | _->None)
      | None-> None)
      | TmIsNil(ty1,ter1) -> (match ter1 with 
        | TmNil(ty2)-> Some(TBool)
        |_ -> type_of (g)(ter1))
      | TmAbs(s,typ1,t1) ->(match type_of (Gam(s,typ1,g))(t1) with
          |Some (a) -> Some(TFun(typ1,a))
          |None -> None) 
      | TmApp(t1,t2) -> (match type_of (g)(t2) with
        | Some(a) ->(match type_of (g)(t1) with 
        |Some(TFun(b,c))-> if(a==b) then Some(c) else None
        | _->None)
        | None-> None)
      | TmIf(t1,t2,t3)-> (match type_of (g)(t1) with
        |Some (TBool)->(match type_of (g)(t2) with
        | Some(ta1)-> (match type_of (g)(t3) with
        | Some(ta2)-> if type_eqv(ta1)(ta2) then Some(ta1) else None
        | _ ->None) 
        | _ ->None)
        | _-> None)
      | TmFst(TmPair(x,y))-> type_of (g)(x)
      | TmSnd(TmPair(x,y))-> type_of (g)(y)
      | TmTail(typ1,t1) -> if list_consistency(t1)(typ1) then Some(TList(typ1)) else None
      | TmCons(typ1,curr,next) -> Some(TList(typ1)) 
      | TmHead(typ1,t1)->  if list_consistency(t1)(typ1) then Some(TSum(TUnit, typ1)) else None
      | TmSucc(t1)-> (match type_of (g)(t1) with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmPred(t1)-> (match type_of g t1 with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmIsZero(t1)-> (match type_of g t1 with
          |Some (TNat) ->  Some(TBool)
          |Some (TFun(a,TNat)) ->Some(TFun(a,TBool))
          |_ -> None)
      | TmCase(t1, s1, t2, s2, t3) -> (match t1 with
      | TmInl(ty,ter) -> (match (type_of g ter) with 
        | Some (a)-> if type_eqv(ty)(a) then Some(a) else None 
        | _-> None)
      | TmInr(ty,ter)-> (match (type_of g ter) with 
      | Some (a)-> if type_eqv(ty)(a) then Some(a) else None 
      | _-> None)
      |_-> None)
      |_->  None;;


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
    let _ = print_endline ("----- Type Checking -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline (": " ^ (opt_typ_to_string (type_of empty_ctx ast))) in
    print_endline "";;


interpret Sys.argv.(1)
