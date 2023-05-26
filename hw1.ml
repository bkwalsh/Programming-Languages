exception No_solution 
exception Invalid_argument 

(* Problem 1: The Collatz Sequence *)

(* Let f(n) = n/2     if n is even
              3n+1    otherwise     *)

(* The Collatz conjecture states that every n > 0, 
   repeated application of f to n terminates in 1. 
   Compute the Collatz sequence [n, f(n), ..., 1] for arbitrary n. 
   Throw an Invalid_argument exception if a number less than 1 is provided. *)

(* helper function that builds list, start with empty list input*)
let rec collatz_list_help n lst =
  if n <= 0 then raise Invalid_argument else
    if n == 1 then n::lst else 
      match (n mod 2) with
      | 0 -> n:: collatz_list_help (n/2) lst
      | 1 -> n :: collatz_list_help (3*n +1) lst
      | _ -> raise Invalid_argument ;;

let rec collatz_list n =
  collatz_list_help n []


(* Helper function to recursively count list length, intended input is
collatz_list as lst*)
 
let rec col_helper (lst : int list) : int =
  match lst with 
  | []->0
  | x :: lst' -> 1 + col_helper lst';; 


(* Now compute the length of the Collatz sequence. *)
let rec collatz_length (n : int) : int =
  col_helper (collatz_list_help n [] );; 


(* Problem 2: Binary search trees *)

(* Consider the following tree type *)
type 'a tree = Nil | Node of 'a tree * 'a * 'a tree 

(* Write a function that tests whether a tree is a valid binary search tree using the built-in '<' operation *)

(* helper function used for valid_bst, validates a single given node by 
checking every node below it for BST property (left side nodes are
 less, right side nodes are more) *)
let rec valid_node (t: 'a tree)(vx : 'a): bool=
  let rec left_min(t: 'a tree)(vx : 'a): bool=
  match t with
  | Nil -> true
  | Node (l,v,r) ->(v < vx &&
  left_min (l) (vx) && left_min (r) (vx)) 
  and right_max(t : 'a tree)(vx: 'a): bool=
    match t with
    | Nil -> true
    | Node (l,v,r) -> (vx < v &&
    right_max (l) (vx) && right_max (r) (vx))
  in
  match t with 
      | Nil -> true
      | Node (l,v,r) -> left_min(l)(v) && right_max (r)(v);;


(* recursively calls valid_node on every node and returns false if any node
   is false *)
let rec valid_bst (t : 'a tree) : bool =
  match t with 
  | Nil -> true
  | Node (l,v,r) -> if (valid_node(t)(v)) then valid_bst(l)&&valid_bst(r) 
    else false;


(* Problem 3: Searching a tree *)

(* We define directions as follows *)

type direction = Left | Right

(* These direction can be used to traverse the trees above. 
   Write a function to return the element at the indicated spot. 
   The end of the input list means to stop. 
   
   Since this will often fail, write versions that 
   1. raise a Not_found exception, and
   2. return a default element,
   3. return an option type.
   *)

let rec search_tree_exn (t : 'a tree) (ds : direction list) : 'a = 
  match t with 
  | Nil -> raise Not_found
  | Node (l,v,r) -> match ds with
      | [] -> v
      | x :: l' -> match x with 
        | Left -> search_tree_exn (l) (l')
        | Right -> search_tree_exn (r) (l') ;;

let rec search_tree_def (t : 'a tree) (ds : direction list) (d : 'a) : 'a = 
  match t with 
  | Nil -> d
  | Node (l,v,r) -> match ds with
      | [] -> v
      | x :: l' -> match x with 
        | Left -> search_tree_def (l) (l') (d)
        | Right -> search_tree_def (r) (l') (d) ;;

type 'a option = | None | Some of 'a;;
let rec search_tree_opt (t : 'a tree) (ds : direction list) : 'a option = 
  match t with 
  | Nil -> None
  | Node (l,v,r) -> match ds with
      | [] -> Some v
      | x :: l' -> match x with 
        | Left -> search_tree_opt (l) (l')
        | Right -> search_tree_opt (r) (l') ;;


(* Problem 4: Summing tree values *)
  
(* For each of the methods above, write a function that takes a list of trees of integers and 
   returns the sum of the values at the given directions. *)

(* throw an exception if any of the trees are missing the desired element *)
let rec sum_tree_exn (ts : int tree list) (ds : direction list) : int = 
  match ts with 
    | []-> 0
    | x :: l' ->  search_tree_exn(x)(ds)+sum_tree_exn(l')(ds) ;;

(* Use 0 as the default here *)
let rec sum_tree_def (ts : int tree list) (ds : direction list) : int = 
  match ts with 
    | []-> 0
    | x :: l' ->  search_tree_def(x)(ds)(0)+sum_tree_def(l')(ds) ;;


(* helper function with curr as running sum for sum_tree_opt, increments curr 
by i whenever finding Some i, else returns none if none. Start at 0 *)
let rec opt_help (ts : int tree list) (ds : direction list) (curr) : 'a option = 
  match ts with 
    | []-> Some curr
    | x :: l' ->  match search_tree_opt(x)(ds) with
      | None -> None 
      | Some i ->  opt_help(l')(ds)(curr+i);; 

(* Return None if any of the trees do. *)
let rec sum_tree_opt (ts : int tree list) (ds : direction list) : 'a option = 
  opt_help(ts)(ds)(0);; 


(* Problem 5: Reversing Lists *)

(* Here is a simple definition of reverse: *)

let rec reverse (l : 'a list) = 
  match l with
  | [] -> []
  | h::t -> reverse t @ [ h ]

(* though correct, this function reverses a list
   in O(n^2) time, since appending to the end of
   a list is done in O(n). It is possible to write
   an alternate definition which can reverse a list
   in linear time. Write such a definition.

   Hint: It will be necessary to write a helper function.
 *)

(* Helper function that mantains curr, current list, and 
   build which is the list to be returned. Iterate through curr
   and add each value to the front of build and return when completed
   curr has length N and (h :: build) is a O(1) operation because 
   it adds to the front of the list which is constant time, so we have
   O(N) runtime*)
 let rec r_f_helper (curr : 'a list) (build: 'a list) =
  match curr with
  | [] -> build 
  | h :: t -> r_f_helper(t)(h :: build) ;;


(* Calls helper function once which is O(N)*)
let reverse_fast (l : 'a list) = 
  r_f_helper(l)([]);;


(* Problem 6: Binary Numbers *)

(* The following is a representation of a binary digit: *)

type digit = Zero | One

(* We can represent a natural number in binary as a list of
   binary digits. Write digits_of_int which converts a machine integer
   into a list of binary digits, where the least significant
   digit is at the head of the list. Raise Negative if the input
   is negative. *)

exception Negative


(* digit helper function, builds list of binary digits, mantaining "place", or 
   value of current binary digit, current some as count, and digits as digit
   list to be returned *)
let rec digits_helper(digits ,count,place) : digit list =
  if count <= 0 then digits  else
      match (count mod place) with
      | 0 -> digits_helper(digits @ [Zero] ,count,(place*2))
      | j -> digits_helper(digits @ [One] ,(count-(count mod place)),(place*2))  

(* calls digits_helper with n' if non-zero, starts binary count at 2*)
let rec digits_of_int (n : int) : digit list = 
  if n < 0 then raise Negative else
    match n with
    | 0 -> [Zero;]
    | n' -> digits_helper([] ,n',2) ;;


let rec int_helper (digits,count,place) : int =
  match digits with
  | []->count
  | x :: xs -> match x with
    | One -> int_helper (xs,count+place,place*2)
    | Zero -> int_helper (xs,count,place*2);;



(* int_of_digits converts a list of digits into a machine integer *)
let rec int_of_digits (digits : digit list) : int = 
  int_helper(digits,0,1);;

(* succ computes the successor of the binary number. For example,
   succ [Zero]      = [One]
   succ [Zero; One] = [One; One]
   succ [One; One]  = [Zero; Zero; One]

   Don't use digits_of_int or int_of_digits in the definition of this function! *)

(* Helper function to check case where there are NO zeros in digit list*)
let rec suc_check_zero (digits : digit list) : bool =
  match digits with 
  | [] -> true
  | x :: xs -> match x with 
    | One -> suc_check_zero (xs)
    | Zero -> false ;;

(* Helper function to check length of  a given digit list*)
let rec suc_get_len (digits : digit list) : int =
  match digits with 
  | [] -> 0
  | x :: xs -> 1 + suc_get_len(xs) ;;

(* Helper function to build a digit list of zeros that is n long*)
let rec suc_build_zeros (n : int) (l : digit list) : digit list =
    match n with 
    | 0 -> l
    | n'-> suc_build_zeros(n'-1)(l @ [Zero]) ;;
    

let rec suc_switch (pre : digit list) (post : digit list): digit list =
  match post with
  | [] -> pre 
  | curr :: xs -> match curr with 
    | One -> suc_switch(pre @ [One]) (xs)
    | Zero -> suc_build_zeros(suc_get_len(pre))([]) @ [One] @ xs ;;   


let rec succ (digits : digit list) : digit list =
  if suc_check_zero(digits) then 
    suc_build_zeros(suc_get_len(digits))([]) @ [One] else
       match digits with 
       | []-> [] @ [One] (* assuming sucessor to empty list is One*)
       | x :: xs -> match x with 
        | Zero -> [] @ [One] @ xs
        | One ->  suc_switch([])(digits);;


(* Problem 7: Tic-Tac-Toe *)

exception Invalid_input

type player = X | O

(* 
  Read the final board of a tic-tac-toe game from a file. Valid input will be of the format:
  `---
   ---
   ---` 
   where each `-` should be `X` or `O`. Raise Invalid_input if input does not match this format.
   Only considering cases where an `X` or an `O` populates every place on the board (so no blank spaces), 
   raise Invalid_input if the board is not a valid end state for a tic-tac-toe game:
    - if there are multiple winners
   Return the winner of this game, if any, as Some winner, where winner : player. 
   If there is no winner, return None.
   You may want to write at least one helper function for this.
 *)

let file_opener_help(filename : string ): string =
  if  Sys.file_exists filename then
  let ic = open_in filename in
  let rec parse_line c=
  try
    let ln = input_line ic in
    parse_line(c^ln^ "\n")
  with End_of_file -> 
    close_in ic;
    c
  in
  parse_line "" 
else raise Invalid_input;;


let rec grid_valid_help(grid : string) (x) : bool =
  if String.length grid <> 12 then raise Invalid_input else
    match x with
    | 11-> true
    | 3 -> if (grid.[x] <> '\n') then raise Invalid_input 
      else grid_valid_help(grid ) (x+1)    
    | 7 -> if (grid.[x] <> '\n') then raise Invalid_input 
      else grid_valid_help(grid ) (x+1)  
    | n' -> if ((grid.[x] == 'X') || (grid.[x] == 'O'))  
      then grid_valid_help(grid ) (x+1) else raise Invalid_input  


let rec search_winner(grid : string) (x) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc): char =
  match x with
  | 12 -> if (ld== 0 ||rd == 0 || tr== 0 || mr==0 || br==0 || lc==0 || mc==0 || rc ==0) then p else 
    'N' 
  | 0 -> if (grid.[0] == p) then search_winner(grid) (x+1) (p) (ld-1) (rd) (tr-1) (mr) (br)
    (lc-1) (mc) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 1 -> if (grid.[1] == p) then search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr-1) (br)
    (lc-1) (mc) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 2 -> if (grid.[2] == p) then search_winner(grid) (x+1) (p) (ld) (rd-1) (tr) (mr) (br-1)
    (lc-1) (mc) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 4 -> if (grid.[4] == p) then search_winner(grid) (x+1) (p) (ld) (rd) (tr-1) (mr) (br)
    (lc) (mc-1) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 5 -> if (grid.[5] == p) then search_winner(grid) (x+1) (p) (ld-1) (rd-1) (tr) (mr-1) (br)
    (lc) (mc-1) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 6 -> if (grid.[6] == p) then search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br-1)
    (lc) (mc-1) (rc) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 8 -> if (grid.[8] == p) then search_winner(grid) (x+1) (p) (ld) (rd-1) (tr-1) (mr) (br)
    (lc) (mc) (rc-1) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 9 -> if (grid.[9] == p) then search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr-1) (br)
    (lc) (mc) (rc-1) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | 10 -> if (grid.[10] == p) then search_winner(grid) (x+1) (p) (ld-1) (rd) (tr) (mr) (br-1)
    (lc) (mc) (rc-1) else search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc)
  | n -> search_winner(grid) (x+1) (p) (ld) (rd) (tr) (mr) (br)
  (lc) (mc) (rc) ;;  

let get_winner (filename : string) : player option =
  let txt = file_opener_help(filename) in 
  if (grid_valid_help(txt)(0)) then
    let check_x=search_winner(txt)(0)('X')(3)(3)(3)(3)(3)(3)(3)(3) in
    let check_o=search_winner(txt)(0)('O')(3)(3)(3)(3)(3)(3)(3)(3) in
     (if ((check_x== 'X') && (check_o== 'O')) then raise Invalid_input else 
      (if (check_x== 'X') then Some X else 
        (if (check_o= 'O') then 
          Some O else None))) else None;;
