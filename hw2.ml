open List
open Char
open Format

exception Not_implemented
exception Parse_exn

(* Data Definitions *)

type token
= LParen
| RParen
| TokTrue
| TokFalse
| TokZero
| TokIf
| TokSucc
| TokPred
| TokIsZero
| TokAnd
| TokOr
| TokNot

type term
= True
| False
| Zero
| If of term * term * term
| Succ of term
| Pred of term
| IsZero of term
| And of term * term
| Or of term * term
| Not of term

(* A term in normal form is either a Value or Stuck. *)
type normal_form
= Value of term
| Stuck of term

(* Utilities *) 

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* Value Judgements *)

(* Returns true if the term is a numeric value, false otherwise. *)
let rec is_num_val (t: term) : bool = 
  match t with 
  | Zero -> true
  | Pred Zero-> false 
  | Pred p -> is_num_val p
  | Succ s -> is_num_val s
  | _ -> false

(* Returns true if the term is a value, false otherwise. *)
let is_val (t: term) : bool = 
  match t with
  | Pred Zero-> false 
  | True -> true
  | False -> true
  | Zero -> true
  | Succ s -> is_num_val s
  | Pred p -> is_num_val p
  | _ -> false 

(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters
   - throw an exception if the characters cannot be tokenized 
  Some basic cases have been given for you. *)
let rec nextToken (cs: char list) : (token * char list) option = 
  match cs with
  | [] -> None
  | ' ':: tl -> nextToken tl
  | '('::tl -> Some (LParen, tl)
  | ')'::tl -> Some (RParen, tl)
  | 't'::'r'::'u'::'e'::tl -> Some (TokTrue, tl)
  | 'f'::'a'::'l'::'s'::'e'::tl -> Some (TokFalse, tl)
  | '0'::tl -> Some (TokZero, tl)
  | 'i'::'f'::tl -> Some (TokIf, tl)
  | 's'::'u'::'c'::'c'::tl -> Some (TokSucc, tl) 
  | 'p'::'r'::'e'::'d'::tl -> Some (TokPred, tl)
  | 'i'::'s'::'z'::'e'::'r'::'o'::tl -> Some (TokIsZero, tl)
  | 'a'::'n'::'d'::tl -> Some (TokAnd, tl)
  | 'o'::'r'::tl -> Some (TokOr, tl)
  | 'n'::'o'::'t'::tl -> Some (TokNot, tl)
  | _ -> raise Parse_exn


(* helper function for scan, calls next token and mantains 'build' which
   is a list of tokens. Initially empty list and as moves through eventually 
   returns build as list of tokens  *)
let rec scan_help(ls: char list)(build: token list): token list =
  match ls with 
  | []-> build
  | _ -> match nextToken ls with
    | None -> build
    | Some(t,tl) -> scan_help tl (build @ [t]);; 

(* turn a string of code (like "(pred 0)" into a list of tokens (like [LParen, TokPred, TokZero, RParen]) *)
let rec scan (ls : char list) : token list =
  scan_help ls [];; (* call scan_help with empty list*)


(* Parser *)

(* list term helper function for grabbing list after term if term has a parens*)
let rec listTermParens (ts)(parencount) =
  match ts with 
  | []-> [] 
  | x :: xs -> (match x with
    | RParen-> if (parencount-1==0) then xs 
      else listTermParens xs (parencount-1)
    | LParen -> listTermParens xs (parencount+1)
    | _ -> listTermParens xs (parencount));;

(* helper function to return term list after a term for building term purposes*)
let rec listTerm (ts) =
  match ts with 
  | []-> []
  | x :: xs -> (match x with
    | TokTrue-> xs
    | TokFalse-> xs
    | TokZero-> xs
    | _ -> listTermParens xs 1);;



(* check if a term has a valid number of parens*)
let rec valid_paren(ts)(parencount) : (bool)=
    match ts with 
    | [] -> if parencount==0 then true else false
    | x :: xs -> (match x with
      | RParen-> if (parencount-1==0) then true 
      else valid_paren xs (parencount-1)
    | LParen -> valid_paren xs (parencount+1)
    | _ ->valid_paren xs (parencount));;


(* next term helper function*)
let rec nextTermHelp (ts) : (term) = 
  match ts with 
    | x :: xs  -> (match x with
    | TokTrue -> True
    | TokFalse -> False
    | TokZero -> Zero 
    | LParen -> if (valid_paren xs 1) then (match xs with 
      | p ::ps -> (match p with
        | TokTrue->raise Parse_exn
        | TokFalse->raise Parse_exn
        | TokZero->raise Parse_exn
        | TokPred -> (Pred (nextTermHelp ps))
        | TokIsZero -> (IsZero (nextTermHelp ps))
        | TokSucc -> (Succ (nextTermHelp ps))
        | TokNot -> (Not (nextTermHelp ps))
        | TokIf -> If (nextTermHelp ps,(nextTermHelp (listTerm ps)), 
        (nextTermHelp (listTerm(listTerm ps))))
        | TokAnd -> And (nextTermHelp ps, (nextTermHelp (listTerm ps)))
        | TokOr -> Or (nextTermHelp ps, (nextTermHelp (listTerm ps))) 
        | _ ->raise Parse_exn)
      | _ ->nextTermHelp xs) else raise Parse_exn 
    | _ -> raise Parse_exn)  
  | _ -> raise Parse_exn;;
    

(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)
let rec nextTerm (ts: token list) : (term * token list) option =
  match ts with 
  | []-> None
  | x :: xs -> (match x with
    | TokTrue -> Some (True, xs)
    | TokFalse-> Some (False, xs)
    | TokZero-> Some (Zero, xs)
    | LParen ->Some(nextTermHelp ts,listTermParens xs 1) 
    | _ -> raise Parse_exn)


(* turn a list of tokens (like [LParen ,TokPred, TokZero, RParen] into a term (like Pred 0) *)
let parse (tokens : token list) : term =
  let x=nextTerm(tokens) in match x with 
  | Some(t,a)-> t
  | _ -> raise Parse_exn;;


(* Small Step evaluator *)

(* small_num_val_step: addresses smallstep for num_val if step is possible*)
let rec small_num_val_step(t) : term option=
  match t with
  | Zero-> None (* returns none because no small steps can be made*)
  | (Succ(Pred(x)))-> Some x
  | (Pred(Succ(x)))-> Some x
  | (Succ(x))->small_num_val_step x
  | (Pred(x))->small_num_val_step x
  | _-> raise Parse_exn (* should only be given number vals*)


(* edge case, checking for edge case of big_num_val_step not fully evaluating.
   this could occur in the case of several preds then several succs, where only
   one succ(pred (... is reduced, so use this 
   function to see if big_num_val_step should be run again reevaluated *)
let rec full_step_num_check(t : term ) : bool=
  match t with
  | Zero -> true
  |(Succ(Pred(x))) -> false (* situation where further reduction is possible*)
  |(Pred(Succ(x))) -> false (* situation where further reduction is possible*)
  |(Succ(x))->full_step_num_check x
  |(Pred(x))->full_step_num_check x
  |_ -> raise Parse_exn;;


(* similar helper function as above but for big step num_val evaluation*)
let rec big_num_val_step(t) : term=
  match t with
  | Zero-> Zero (* returns zero because no more small steps*)
  | (Succ(Pred(x)))-> big_num_val_step x
  | (Pred(Succ(x)))-> big_num_val_step x
  | (Succ(x))->Succ(big_num_val_step x)
  | (Pred(x))->Pred(big_num_val_step x)
  | _-> raise Parse_exn (* should only be given number vals*)

(* small step helper recursive function to deal with type for nested cases
   implimented so all cases should step based on small_step fn*)
let rec small_step_help(t: term) : term =
  match t with
  | Pred Zero ->  Zero (* evaluates to zero case*)
  | If (True,b,c) -> b
  | If (False,b,c) -> c
  | If (a,b,c)  -> If (small_step_help a,b,c)
  | And (True,x) -> x
  | And (False,b) -> False
  | Or (False,b) -> b 
  | Or (True,b) -> True 
  | Or (a,b) -> Or (small_step_help a,b)
  | Not (True) -> False  
  | Not (False) -> True
  | Not (a) -> Not(small_step_help a)
  | IsZero (Zero) -> True  
  | IsZero (a) -> if (is_val a) then raise Parse_exn
     else IsZero(small_step_help a) 
  | _ ->raise Parse_exn;;

(* Implement the small-step evaluation relation from class. 
   For And, Or and Not, you should be able to determine 
   appropriate rules by extrapolating from the If rules.
   If a term is not a normal form, take the next possible step
   - i.e., if t -> u, then step(t) should return Some(u)
   if a term is a normal form, return None *)
let rec small_step (t : term) : term option =
  if (is_num_val t) then small_num_val_step t else
  match t with (* error checking for vals that don't step *)
  | True -> None
  | False -> None
  | Zero -> None 
  | If (Zero,b,c) -> None
  | IsZero(True) -> None
  | IsZero(False) -> None
  | And (Zero,a) -> None
  | And (False,Zero) -> None
  | Or (Zero,b) -> None
  | Not (Zero) -> None
  | _ ->Some (small_step_help t);;


(* Returns true if the term is stuck, false otherwise. *)
let is_stuck (t: term) : bool = 
  match t with
  (* check bad inputs with respect to short circuting*)
  | If (Zero,b,c) -> true
  | And(Zero,b) -> true
  | Or(Zero,b) -> true 
  | Not(Zero) -> true
  | IsZero(True) -> true
  | IsZero(False) -> true
  (* can step *)
  | If (a,b,c) -> false
  | IsZero(a) -> false
  | And(a,b) -> false
  | Or(a,b) -> false 
  | Not(a) -> false
  | Pred(Zero) -> false 
  (* check if a value*)
  | _-> if (is_val t) then false else true;; 


(* Returns true if the term is a normal form, false otherwise. *)
  let is_normal (t: term) : bool =  
    (* checks if stuck or value*)
    (is_stuck t) || (match t with
    | (Succ Zero)-> true 
    | True -> true
    | False-> true
    | Zero -> true
    | _-> false);;


(* Given t, return t' such that t ->* t' and t' is a normal form. *)
let rec multistep_full (t : term) : term =
  if (is_normal t) then t else (* check if any steps can be made*)
    (if(is_num_val t) then 
      (if (full_step_num_check(big_num_val_step t)) (* consider num_val case*)
        then big_num_val_step t else 
          multistep_full(big_num_val_step t)) (* check edge case of calling big_num_val_step again*)
     else multistep_full(small_step_help t)) ;;

(* Returns true if a term steps to a value, and false otherwise. *)
let rec multisteps_to_value (t: term) : bool = 
  is_val(multistep_full t);;
  

(* Big Step evaluator *)

(* Now implement the big-step relation from class. 
   Again, return none if the program doesn't (big) step. *)
let rec big_step (t : term) : term option =
  if(is_num_val t) then Some (big_num_val_step t) else (* make step if nonzero*)
    if (is_val t) then Some t (* if val, already normal form*)
    else if (multisteps_to_value t) then Some (multistep_full t) else None;;

(* Interpreter *)

(* You should not need to modify this code -- feel free to add statements for debugging,
   but remember to delete them before submitting. *)

let rec term_to_string (t : term) : string = match t with
| True -> "true"
| False -> "false"
| Zero -> "zero"
| If (t1, t2, t3) -> "(" ^ "if " ^ term_to_string t1 ^ " then " ^ term_to_string t2 ^ " else " ^ term_to_string t3  ^ ")"
| Succ (t1) -> "(" ^ "succ " ^ term_to_string t1 ^ ")"
| Pred (t1) -> "(" ^ "pred " ^ term_to_string t1 ^ ")"
| IsZero (t1) ->  "(" ^ "iszero " ^ term_to_string t1 ^ ")"
| And (t1, t2) -> "(" ^ term_to_string t1 ^ " and " ^ term_to_string t2 ^ ")"
| Or (t1, t2) -> "(" ^ term_to_string t1 ^ " or " ^ term_to_string t2 ^ ")"
| Not (t1) -> "(" ^ "not " ^ term_to_string t1 ^ ")"

let opt_term_to_string (o : term option) : string = 
  match o with
  | None -> " "
  | Some t -> term_to_string t 

let interpret (str : string) : unit =
  let chars = string_to_char_list str in
  let tokens = scan chars in
  let ast = parse tokens in
  let ss_term = small_step ast in
  let bs_term = big_step ast in
  let term_str = term_to_string ast in 
  let ss_term_str = opt_term_to_string ss_term in
  let bs_term_str = opt_term_to_string bs_term in
  let _ = print_endline ("----- Small Step Evaluation -----") in
  let _ = print_endline ("      " ^ term_str) in 
  let _ = print_endline ("->    " ^ ss_term_str) in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline ("----- Big Step Evaluation -----") in
  let _ = print_endline ("      " ^ term_str) in 
  print_endline ("||" ^ bs_term_str);;


interpret Sys.argv.(1)
