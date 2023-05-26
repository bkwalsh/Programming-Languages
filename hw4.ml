module SS = Set.Make(String)

open List
open Char
open Format


exception Not_implemented
exception Parse_exn
exception NotAbs of string
exception NotFound of string
exception DuplicateVar of string

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
| TokTrue
| TokFalse

type typ 
= TBool
| TNat 
| TFun of typ * typ

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

(* Utilities *) 

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* Lexical Scanner *)

(* helper functions*)

(* lowercase char check*)
let is_lowercase (c:char) : bool =
  Char.code c >= Char.code 'a' && Char.code c <= Char.code 'z'

(* letter check*)
let is_letter c =
  let cd = Char.code c in
  (cd >= 65 && cd <= 90) || (cd >= 97 && cd <= 122)

(* is a digit check*)
let is_digit c =
  let cd = Char.code c in
  cd >= 48 && cd <= 57

(*handles variables, inurrupt on withspace, otherwise adding to string *)
let rec var_help(cs)(build) : (string) =
  match cs with
  | []-> build
  | ' ':: tl -> build
  | c :: tl -> if ((is_letter c) || (is_digit c)) then
    var_help(tl)(build^ (String.make 1 c)) else build;;

(* same as above but returns character list after instead*)
let rec var_list(cs) : (char list) =
  match cs with
  | []-> []
  | ' ':: tl -> cs
  | c :: tl -> if ((is_letter c) || (is_digit c)) then
    var_list(tl) else cs;;

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters (except inside strings)
   - throw an exception if the characters cannot be tokenized *)
let rec nextToken (cs: char list) : (token * char list) option = 
  match cs with 
  | []-> None 
  | ' ':: tl -> nextToken tl
  | '('::tl -> Some (LParen, tl)
  | ')'::tl -> Some (RParen, tl)
  | '&'::tl -> Some (TokLam, tl)
  | '.'::tl -> Some (TokDot, tl)
  | 'I':: 'f' :: tl -> Some (TokIf, tl)
  | 'T':: 'h' :: 'e' :: 'n' :: tl -> Some (TokThen, tl)
  | 'N':: 'a' :: 't' :: tl -> Some (TokNat, tl)
  | 'E':: 'l' :: 's' :: 'e' :: tl -> Some (TokElse, tl)
  | 'B':: 'o' :: 'o' :: 'l' :: tl -> Some (TokBool, tl)
  | 'T':: 'r' :: 'u' :: 'e' :: tl -> Some (TokTrue, tl)
  | 'F':: 'a' :: 'l' :: 's' :: 'e' :: tl -> Some (TokFalse, tl)
  | 'S':: 'u' :: 'c' :: 'c' :: tl -> Some (TokSucc, tl)
  | 'P':: 'r' :: 'e' :: 'd' :: tl -> Some (TokPred, tl)
  | 'I':: 's' :: 'Z' :: 'e' :: 'r' :: 'o' :: tl -> Some (TokIsZero, tl)
  | '0':: tl -> Some (TokZero, tl)
  | ':'::tl -> Some (TokColon, tl)
  | '-' ::'>'::tl -> Some (TokArrow, tl)
  | a :: tl -> if (is_lowercase(a)) then 
      Some (TokVar (var_help(cs)("")), var_list(cs))  else raise Parse_exn;;



(* scanner helper, starts with empty char list and addds to it*)
let rec scan_help(ls: char list)(build: token list): token list =
  match ls with 
  | []-> build
  | _ -> match nextToken ls with
    | None -> build
    | Some(t,tl) -> scan_help tl (build @ [t]);; 

(* turn a string of code (like "&x:Bool.x" into a list of tokens (like [TokLam, TokVar("x"), TokColon, TokBool, TokDot, TokVar("x")]) *)
let rec scan (ls : char list) : token list = 
  scan_help ls [];;

(* Parser *)

(* handles parsing types*)
let rec typehelp(ts: token list) : (typ * token list)=
  match ts with
  | []-> raise Parse_exn
  | LParen:: xl -> (match typehelp(xl) with
      | (ty1, toks1) -> (match toks1 with 
      | RParen :: xll -> (match typehelp(xll) with
        | (ty2, toks2) ->(TFun(ty1,ty2), toks2))
      | _ -> raise Parse_exn))

  | TokBool :: TokArrow :: xl -> (match typehelp(xl) with
      | (ty, toks) ->  (TFun(TBool,ty), toks))

  | TokNat :: TokArrow :: xl -> (match typehelp(xl) with
      | (ty, toks) ->  (TFun(TNat,ty), toks))

  | TokBool :: TokDot :: xl ->(TBool, xl)     
  | TokNat :: TokDot :: xl ->(TNat, xl)      
  | _ -> raise Parse_exn
    



let rec nextTermHelper (ts: token list) : (term * token list) =

      (* handles applications*)
  let rec applicationHelper (ts: token list) : (term * token list) =
    match ts with
    | LParen::tl -> (match nextTermHelper(tl) with
    | (t1, toks1) -> (match toks1 with
    | RParen::LParen::tll -> (match nextTermHelper(tll) with
    |  (t2, toks2) -> (match toks2 with
    | RParen::tlll -> (TmApp(t1,t2),tlll)
    | _-> raise Parse_exn))
    | _-> raise Parse_exn ))
    | _-> raise Parse_exn in

    (* handles if case*)
  let rec ifHelp (ts: token list) : (term * token list) =
    match ts with
    | TokIf::tl -> (match nextTermHelper(tl) with
    | (t1, toks1) -> (match toks1 with
    | TokThen::tll -> (match nextTermHelper(tll) with
    |  (t2, toks2) -> (match toks2 with
    | TokElse::tlll -> (match nextTermHelper(tlll) with
    |  (t3, toks3) -> (TmIf(t1,t2,t3),toks3))
    | _-> raise Parse_exn))
    | _-> raise Parse_exn))
    | _-> raise Parse_exn in

    (* handles lambdas*)
  let rec lambdaHelp (ts: token list) : (term * token list) =
    match ts with
    | TokLam:: TokVar(s) :: TokColon ::tl -> (match typehelp(tl) with
    | (ty, toks) -> (match nextTermHelper(toks) with
      (tm,toksx) -> (TmAbs(s,ty, tm), toksx)))
    | _->  raise Parse_exn in


  match ts with
  | []->   raise Parse_exn
  | x :: xs ->(match x with
    | TokTrue -> (TmTrue,xs) 
    | TokFalse ->  (TmFalse,xs) 
    | TokVar(s) -> (TmVar(s),xs)
    | TokZero -> (TmZero,xs) 
    | LParen -> applicationHelper(ts)
    | TokLam -> lambdaHelp(ts)
    | TokIf-> ifHelp(ts)
    | TokSucc -> (match nextTermHelper(xs) with
    | (tm, toks) -> (TmSucc tm),toks)
    | TokPred -> (match nextTermHelper(xs) with
    | (tm, toks) -> (TmPred tm),toks)
    | TokIsZero -> (match nextTermHelper(xs) with
    | (tm, toks) -> (TmIsZero tm),toks)
    | _-> raise Parse_exn
  )


(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)
let rec nextTerm (ts: token list) : (term * token list) option =
  match ts with
  | []-> None
  | x :: xs ->Some(nextTermHelper ts);;

(* turn a list of tokens (like [TokLam, TokVar of "x", TokDot, TokVar of "x"] into a term (like TmAbs ("x", TmVar("x"))) *)
let parse (tokens : token list) : term =
let x=nextTerm(tokens) in match x with 
  | Some(t,[])-> t
  | Some(t,a)-> raise Parse_exn
  | _ ->  raise Parse_exn



(* Alpha Conversion *)

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



(* Get all variables in set and put in string set for alpha_convert *)
let rec fv (t:term) : SS.t =
  let set = SS.empty in
  let rec fv_help (t:term)(set:SS.t): SS.t =
    match t with 
    | TmVar (c) ->  SS.add c set
    | TmAbs(s,typ,t1)->SS.union (SS.add s set) (fv_help(t1)(set))
    | TmApp(t1,t2) -> SS.union (fv_help(t1)(set)) (fv_help(t2)(set))
    | TmIf(t1,t2,t3) ->SS.union(SS.union (fv_help(t1)(set))  
        (fv_help(t2)(set))) (fv_help t3 set)
    | TmSucc(t1) ->fv_help t1 set
    | TmPred(t1) ->fv_help t1 set
    | TmIsZero(t1) ->fv_help t1 set
    | _ -> set in
    fv_help(t)(set);;

(* alpha convert helper given an old string to replace with a newstring*)
let rec alpha_convert_help(t : term)(newstring:string)(oldstring: string): term =
  match t with
  | TmAbs(s,typ,t1) -> if ((String.compare s oldstring)!=0) then 
      TmAbs(s,typ,alpha_convert_help t1 newstring oldstring) else  TmAbs(s,typ,t1)
  | TmVar(s)-> if ((String.compare s oldstring)==0) then TmVar(newstring) 
      else TmVar(s)
  | TmApp(t1,t2)-> TmApp(alpha_convert_help t1 newstring oldstring, 
    alpha_convert_help t2 newstring oldstring)
  | TmIf(t1,t2,t3) ->TmIf(alpha_convert_help t1 newstring oldstring, 
    alpha_convert_help t2 newstring oldstring, 
    alpha_convert_help t3 newstring oldstring)
  | TmSucc(t1) ->TmSucc(alpha_convert_help t1 newstring oldstring)
  | TmPred(t1) ->TmPred(alpha_convert_help t1 newstring oldstring)
  | TmIsZero(t1) ->TmIsZero(alpha_convert_help t1 newstring oldstring)
  | _ -> t



(* takes a term of the form &x:T.t1 and turns it into an equivalent &y:T.t1', where
   y is a fresh variable and t1' is t1 with (free) x's replaced with ys. 
   If t is not a lambda abstraction return a NotAbs exception*)
let alpha_convert  (t : term) (vars : SS.t) : term =
  let newstring=fresh_var(fv(t)) in
  match t with 
  | TmAbs(s,typ,trm) -> TmAbs(newstring,typ,alpha_convert_help trm newstring s)
  | _ -> raise Parse_exn;;




(* Typechecking *)
(* give a reasonable type to context *)
(* approach: use Empty_ctx as a stopping point within a linked list,
   every other context has a typ and string associated and nested type. 
   Some examples:
    Empty_ctx-> ""
   (Gam("y",TBool,Empty_ctx)) -> "y:Bool" 
   (Gam("y",TBool,(Gam("x",TNat,Empty_ctx)))) -> "y:Bool, x:Nat "*)
type ctx
= Empty_ctx
| Gam of string * typ * ctx

(* define the empty context *)
(* here empty_ctx is just the Empty_ctx type from ctx*)
let empty_ctx : ctx = Empty_ctx;;

(* look up a given variable's typ, throw a NotFound exception if the variable is not found *)
let rec lookup (g : ctx) (x : string) : typ =
  match g with
  | Empty_ctx -> raise (NotFound x)
  | Gam(s,ty,prev) -> if ((String.compare s x)==0) 
    then ty else lookup (prev) (x);;



(* extend a context with a new variable-typ association *)
(* throw a DuplicateVar exception if the variable already exists in g *)
(* replacing Empty_ctx with a new variable-typ association at end of 
linked list if no duplicates *)
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

  match t with
      | TmVar(s) ->find_type(g)(s)
      | TmTrue -> Some(TBool)
      | TmFalse-> Some(TBool)
      | TmZero -> Some(TNat)
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

      | TmSucc(t1)-> (match type_of (g)(t1) with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmPred(t1)-> (match type_of (g)(t1) with
          |Some (TNat) -> Some(TNat)
          |Some (TFun(a,TNat)) -> Some(TFun(a,TNat))   
          |_ -> None)
      | TmIsZero(t1)-> (match type_of (g)(t1) with
          |Some (TNat) ->  Some(TBool)
          |Some (TFun(a,TNat)) ->Some(TFun(a,TBool))
          |_ -> None) 




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
