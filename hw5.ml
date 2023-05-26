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

let rec nextToken (cs: char list) : (token * char list) option = 
  raise Not_implemented

let rec scan (ls : char list) : token list = raise Not_implemented

let rec nextTerm (ts: token list) : (term * token list) option = raise Not_implemented

let parse (tokens : token list) : term = raise Not_implemented


(* Derived forms *)

(* Implement the derived forms t;t, let x : T = t in t, option T
   and option case from the book and class. *)
(* In t;t, the first t should have type unit. *)
(* In let, note that x is annotated with a type.  *)
(* option T use a sum type to encode an option type *)
(* option case should case on None and Some t, returning a term for each case *)


let tm_seq (t1 : term) (t2 : term) : term =
  match t1 with
  | TmUnit -> t2
  | _ -> raise Parse_exn;;

let tm_let (x : string) (tp : typ) (t1 : term) (t2 : term) : term = raise Not_implemented 

let tp_opt (tp : typ) : typ = raise Not_implemented 

let tm_some (t :term) : term = raise Not_implemented

let tm_none : term = raise Not_implemented

let tm_opt_case (t: term) (t_some : string -> term) (t_none : term) : term = 
  raise Not_implemented

(* Small-step evaluation *)

(* Implement the small-step evaluation relations from class. 
   Note that we're only concerned with call-by-value for this homework. 
   Feel free to reuse code from homework 3. 
   (Implementing capture-avoiding substitution is encouraged, but not what we 
   will be grading this on) *)

let rec cbv (t : term) : term option = raise Not_implemented

let rec multistep (t : term) : term option = raise Not_implemented

(* Typechecking utilities *)

(* These first few functions can be copied from prior homeworks. 
   We will try to give solutions shortly after the late deadline. *)

(* give a reasonable type to context *)
type ctx = unit 

(* define the empty context *)
let empty_ctx : ctx = raise Not_implemented

(* look up a given variable's typ, throw a NotFound exception if the variable is not found *)
let lookup (g : ctx) (x : string) : typ = raise Not_implemented

(* extend a context with a new variable-typ association *)
let extend (g : ctx) (x : string) (t : typ): ctx = raise Not_implemented


(* Typechecking *)

(* return the type of a term in the given context *)
(* return None if the term is ill-typed *)
let type_of (g : ctx) (t : term) : typ option = raise Not_implemented


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
