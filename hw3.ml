module SS = Set.Make(String)

open List
open Char
open Format

exception Not_implemented
exception Parse_exn
exception CaptureException of string

(* Data Definitions *)

type token
= LParen
| RParen
| TokLam
| TokDot
| TokVar of string

type term
= TmVar of string
| TmAbs of string * term
| TmApp of term * term

(* Utilities *) 

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters
   - throw an exception if the characters cannot be tokenized *)

(*  helper function *)
let is_letter c =
  let cd = Char.code c in
  (cd >= 65 && cd <= 90) || (cd >= 97 && cd <= 122)

let is_digit c =
  let cd = Char.code c in
  cd >= 48 && cd <= 57


let rec var_help(cs)(build) : (string) =
  match cs with
  | []-> build
  | ' ':: tl -> build
  | c :: tl -> if ((is_letter c) || (is_digit c)) then
    var_help(tl)(build^ (String.make 1 c)) else build;;

(* char list after first var*)
let rec var_list(cs) : (char list) =
  match cs with
  | []-> []
  | ' ':: tl -> cs
  | c :: tl -> if ((is_letter c) || (is_digit c)) then
    var_list(tl) else cs;;

let rec nextToken (cs: char list) : (token * char list) option = 
  match cs with
  | [] -> None
  | ' ':: tl -> nextToken tl
  | '('::tl -> Some (LParen, tl)
  | ')'::tl -> Some (RParen, tl)
  | '&'::tl -> Some (TokLam, tl)
  | '.'::tl -> Some (TokDot, tl)
  | c :: tl -> if ((is_letter c) || (is_digit c)) 
    then Some (TokVar (var_help(cs)("")), var_list(cs)) else raise Parse_exn  


let rec scan_help(ls: char list)(build: token list): token list =
  match ls with 
  | []-> build
  | _ -> match nextToken ls with
    | None -> build
    | Some(t,tl) -> scan_help tl (build @ [t]);; 
(* turn a string of code (like "&x.x" into a list of tokens (like [TokLam, TokVar("x"), TokDot, TokVar("x")]) *)
let rec scan (ls : char list) : token list =
  scan_help ls [];; (* call scan_help with empty list*) 

(* Parser *)

(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)

(* checks for valid paren for a term list*)
let rec valid_paren(ts)(parencount) : (bool)=
  match ts with 
  | [] -> if parencount==0 then true else false
  | x :: xs -> (match x with
  | RParen-> if (parencount-1==0) then true 
  else valid_paren xs (parencount-1)
  | LParen -> valid_paren xs (parencount+1)
  | _ ->valid_paren xs (parencount));;


(* returns term list after term based on parens*)
let rec listTermParens (ts)(lcount)(rcount) =
  match ts with 
  | []-> [] 
  | x :: xs -> (match x with
    | RParen-> if (rcount==1 && lcount==0) then xs 
      else listTermParens xs (lcount)(rcount-1)
    | LParen -> if (lcount==0) then 
      listTermParens xs(lcount+1)(rcount+2) else 
        listTermParens xs (lcount-1)(rcount)
    | _ ->  listTermParens (xs)(lcount)(rcount));;

(* returns term list after a term*)
let rec nextTermlist (ts)(count) =
  match ts with 
  | []-> []
  | x :: xs -> (match x with
    | TokVar s-> if (count==0) then xs else nextTermlist (xs)(count-1)
    | TokLam -> nextTermlist(xs)(count+1)
    | LParen -> listTermParens ts 2 2
    | _ -> nextTermlist (xs)(count));;
  

(* gets next string from term list, designed for designed for TmAbs*)
let rec grabVar (ts) : string =
  match ts with 
  | []-> raise Parse_exn
  | x :: xs -> (match x with
    | TokVar s-> s
    | _ -> raise Parse_exn);;


(* skips var and returns token list after, designed for designed for TmAbs*)
let skipVar(ts'): (token list)=
  match ts' with
  | []-> []
  | x :: xs -> (match x with
  | TokVar s-> (match xs with 
  |xx :: xxs -> (match xx with
  | TokDot-> xxs
  |_ -> raise Parse_exn)
  | _-> raise Parse_exn) 
  | _ -> raise Parse_exn)


(* gets term after set of parens (second term in TmApp)*)
let rec after_parens_term(ts)(lcount)(rcount): (token list) =
  match ts with 
  | []-> [] 
  | x :: xs -> (match x with
    | RParen-> if (rcount==1 && lcount==0) then (match xs with
      | xx:: xxs -> xxs
      | []-> raise Parse_exn) 
      else after_parens_term xs (lcount)(rcount-1)

    | LParen -> if (lcount==0) then 
      after_parens_term xs(lcount+1)(rcount+2) else 
        after_parens_term xs (lcount-1)(rcount)
    | _ ->  after_parens_term (xs)(lcount)(rcount));;


(* gets next term as a helper function*)
let rec nextTermHelp (ts) : (term) =
  match ts with 
    | x :: xs  -> (match x with
    | TokVar s -> TmVar s
    | TokDot-> raise Parse_exn
    | TokLam -> TmAbs (grabVar(xs), nextTermHelp((skipVar(xs))))
    | LParen -> TmApp((nextTermHelp xs, (nextTermHelp (after_parens_term(xs)(0)(1)))))
    | RParen -> nextTermHelp xs)
    | _ ->  raise Parse_exn;;


let rec nextTerm (ts: token list) : (term * token list) option =
  match ts with 
  | []-> None 
  | x :: xs-> (match x with
    | TokVar s -> Some(TmVar s ,xs)
    | _ -> Some (nextTermHelp(ts),nextTermlist ts 0));;



(* turn a list of tokens (like [TokLam, TokVar of "x", TokDot, TokVar of "x"] into a term (like TmAbs ("x", TmVar("x"))) *)
let parse (tokens : token list) : term =
  if valid_paren(tokens)(0) then
  (let x=nextTerm(tokens) in match x with 
  | Some(t,a)-> t
  | _ -> raise Parse_exn) else raise Parse_exn;;






(* Substitution *)

(* Implement the substitution function `[x |-> s] t` discussed in class. 
   If substitution would result in variable capture, simply 
   raise a CaptureException (with the message string of your choice). *)

(* builds set given set, helper for fv*)
let rec fv_help (t:term)(set:SS.t): SS.t =
  match t with 
  | TmVar (c) ->  SS.add c set
  | TmAbs(s,t) ->SS.remove s (fv_help(t)(set))
  | TmApp(t1,t2) -> SS.union (fv_help(t1)(set)) (fv_help(t2)(set))

(* Get the free variables of t as a string set . *)
let rec fv (t:term) : SS.t =
  let set = SS.empty in 
  match t with 
  | TmVar (c) ->  SS.add c set
  | TmAbs(s,t) ->SS.remove s (fv_help(t)(set))
  | TmApp(t1,t2) -> SS.union (fv_help(t1)(set)) (fv_help(t2)(set));;

(* CaptureException of string*)
let rec subst (x : string) (s : term) (t : term) : term = 
  let set=fv(s) in
  match t with 
  | TmVar c -> if ((String.compare c x)==0) then s else  t
  | TmAbs(cc,t1) -> if ((String.compare cc x)==0) then t else  if (SS.mem cc set) then
    raise (CaptureException "error") else TmAbs(cc,subst x s t1)
  | TmApp(t2,t3) -> TmApp(subst x s t2,subst x s t3);;

(* Small-step evaluation *)

(* Implement the small-step evaluation relations from class. 
   We will implement both variants from class: call-by-name and
   call-by-value. 
   We will also implement a third approach: Full beta reduction,
   which reduces terms under a lambda. 
   Return none if a term doesn't step. *)



let rec cbn (t : term) : term option =
  (* recursion helper*)
  let rec cbn_h(t : term) : term =
    match t with 
    | TmVar (s) -> TmVar (s)
    | TmAbs (s1, t1) -> TmAbs (s1, cbn_h t1) 
    | TmApp (TmAbs (s2, t4), t5) -> subst s2 t5 t4
    | TmApp (t2, t3) -> TmApp(cbn_h t2, t3) in 

  match t with 
  | TmVar (s) -> None
  | TmAbs (s1, t1) -> None
  | TmApp (t2, t3) -> Some (cbn_h t)


    
let rec cbv (t : term) : term option =
  (* recursion helper*)
  let rec cbv_h(t : term) : term =
    match t with 
    | TmVar (s) -> t
    | TmAbs (s1, t1) -> t
    | TmApp (TmAbs (s2, t4), TmVar (s) ) -> subst s2 (TmVar (s)) (cbv_h t4)
    | TmApp (TmAbs (s2, t4), TmAbs (s1, TmVar (s))) -> subst s2 (TmAbs (s1, TmVar (s))) (cbv_h t4)
    | TmApp (TmAbs (s2, t4), t5) -> subst s2 (cbv_h t5) t4
    | TmApp (TmVar (s), t3) -> TmApp(TmVar (s), cbv_h t3)
    | TmApp (t2, t3) -> TmApp(cbv_h t2,  cbv_h t3) in

  match t with 
  | TmApp (TmAbs (s2, t4), TmApp (t2, t3))->Some(TmApp (TmAbs (s2, t4), t2))
  | TmApp (TmAbs (s2, t4), TmAbs (s1, t3))->Some(subst s1 t3 t4)
  | TmApp (TmApp (t2, t3), a) -> Some(TmApp (t2, a))
  | _ -> None 


  let succ = TmAbs ("n", TmAbs ("f", TmAbs ("x", TmApp (TmVar "f", TmApp (TmApp (TmVar "n", TmVar "f"), TmVar "x")))))

  let plus = TmAbs ("n", TmAbs ("m", TmAbs ("f", TmAbs ("x", TmApp (TmApp (TmVar "n", TmVar "f"), TmApp (TmApp (TmVar "m", TmVar "f"), TmVar "x"))))))
  
  let mult = TmAbs ("n", TmAbs ("m", TmApp (TmVar "n", TmVar "m")))
  
  let fix = TmAbs ("f", TmApp (TmAbs ("x", TmApp (TmVar "f", TmApp (TmVar "x", TmVar "x"))), TmAbs ("x", TmApp (TmVar "f", TmApp (TmVar "x", TmVar "x")))))
  
  let pred = TmAbs ("n", TmAbs ("f", TmAbs ("x", TmApp (TmApp (TmApp (TmVar "n", TmAbs ("g", TmAbs ("h", TmApp (TmVar "h", TmApp (TmVar "g", TmVar "f"))))), TmAbs ("u", TmVar "x")), TmAbs ("u", TmVar "u")))))
  
  let is_zero = TmAbs ("n", TmAbs ("t", TmAbs ("f", TmApp (TmApp (TmVar "n", TmAbs ("u", TmVar "f")), TmVar "t"))))
  
  let zero = TmAbs ("f", TmAbs ("x", TmVar "x"))
  let one = TmAbs ("f", TmAbs ("x", TmApp (TmVar "f", TmVar "x")))
  let two = TmAbs ("f", TmAbs ("x", TmApp (TmVar "f", TmApp (TmVar "f", TmVar "x"))))
  
  let rec_fact = TmAbs ("f", TmAbs ("n", TmApp (TmApp (TmApp (is_zero, TmVar "n"), one), TmApp (TmApp(mult, TmVar "n"), TmApp (TmVar "f", TmApp (pred, TmVar "n"))))))
  
  let fact = TmApp (fix, rec_fact)
  
let k=TmApp(TmApp(TmApp(plus, one), two), TmApp(TmApp(mult, one), two)) |> cbv;; 
raise Parse_exn

let rec beta (t : term) : term option =
  (* recursion helper*)
  let rec beta_h(t : term) : term =
    match t with 
    | TmVar (s) -> t
    | TmApp (TmVar (s1),TmVar (s2)) -> t
    | TmAbs (s1, t1) -> TmAbs (s1, beta_h t1) 
    | TmApp (TmAbs (s2, t4), t5) -> (subst s2 (beta_h t5) t4) 
    | TmApp (t2, t3) -> TmApp (beta_h t2, beta_h t3) in
    (* sets stopping point to return None, used to see when no more evaluation possible*)
    let rec betastop (t: term) : bool=
      match t with 
      | TmVar (s) -> true
      | TmAbs (s1, TmVar (s2)) -> if ((String.compare s1 s2)==0) then true else false
      | TmAbs (s1, (TmApp (TmVar (s2),TmVar (s3)))) -> true
      | TmAbs (s1, TmAbs (s2, t1)) -> betastop t1
      | TmApp (TmVar (s1),TmVar (s2))-> true  
      | _ -> false in

   if betastop(t) then None else
    match t with
    | TmVar (s) -> None
    | TmAbs (s1, TmVar (s2)) -> None
    | TmAbs (s1, t1) -> Some(TmAbs (s1, beta_h t1))
    | TmApp (TmVar (s1),TmVar (s2))-> None  
    | _ -> Some (beta_h t);; 


(* Given an evaluation strategy above and a term t, return t' 
  such that t ->* t' and t' is a normal form for the given evaluation 
  strategy. *)

(* helper function to take out t' from Some t'*)
let rec takeOutTerm (t:term option): term=
match t with 
| None -> raise Parse_exn (* should always be given valid terms, raise error if not*)
| Some t' -> t'

let rec multistep (strat : term -> term option) (t : term) : term =
  match strat t with
   | None -> t
   | Some t'-> multistep strat (takeOutTerm(Some t'));; 


(* Define the boolean terms true and false as given in class.
  (We'll use the book's `tru` and `fls` to avoid notation clashes.)
   Define a lambda term that implements an `xor` operation on bools. *)

let rec tru : term = TmAbs("t",TmAbs("f",TmVar ("t")));; 

let rec fls : term = TmAbs("t",TmAbs("f",TmVar ("f")));; 

let rec xor=  TmAbs ("i",TmAbs ("j",TmApp (TmApp (TmVar "i",TmAbs ("t",TmAbs ("f", TmApp (TmApp (TmVar "j", TmVar "f"), TmVar "t")))),TmVar "j")))

(* Interpreter *)

(* You should not need to modify this code -- feel free to add statements for debugging,
   but remember to delete them before submitting. *)

let rec term_to_string (t : term) : string = match t with
| TmVar(str) -> str
| TmAbs(var, body) -> "&" ^ var ^ "." ^ (term_to_string body)
| TmApp(t1, t2) -> "(" ^ (term_to_string t1) ^ ") (" ^ (term_to_string t2) ^ ")"

let opt_term_to_string (o : term option) : string = 
  match o with
  | None -> " "
  | Some t -> term_to_string t 

  let interpret (str : string) : unit =
    let chars = string_to_char_list str in
    let tokens = scan chars in
    let ast = parse tokens in
    let term_str = term_to_string ast in
    let _ = print_endline ("----- Call by Name Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (opt_term_to_string (cbn ast))) in
    let _ = print_endline "" in
    let _ = print_endline "-----------------------------------" in
    let _ = print_endline "" in
    let _ = print_endline ("----- Call by Name Multistep Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (term_to_string (multistep cbn ast))) in
    let _ = print_endline "" in
    let _ = print_endline "-----------------------------------" in
    let _ = print_endline "" in
    let _ = print_endline ("----- Call by Value Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (opt_term_to_string (cbv ast))) in
    let _ = print_endline "" in
    let _ = print_endline "-----------------------------------" in
    let _ = print_endline "" in
    let _ = print_endline ("----- Call by Value Multistep Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (term_to_string (multistep cbv ast))) in
    let _ = print_endline "" in
    let _ = print_endline "-----------------------------------" in
    let _ = print_endline "" in
    let _ = print_endline ("----- Full Beta Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (opt_term_to_string (beta ast))) in
    let _ = print_endline "" in
    let _ = print_endline "-----------------------------------" in
    let _ = print_endline "" in
    let _ = print_endline ("----- Full Beta Multistep Evaluation -----") in
    let _ = print_endline ("      " ^ term_str) in 
    let _ = print_endline ("->    " ^ (term_to_string (multistep beta ast))) in
    print_endline "";;


interpret Sys.argv.(1)
