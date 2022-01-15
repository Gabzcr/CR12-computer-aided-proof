




exception BadValue;; (* This exception means that something else than a bit 0 or 1 was read. *)
exception Empty;; (* This means a word (as a predefined array of -1) lacks a letter at an observed position. *)
exception Sortir0;; (* Same but the word is in a global variable array, so no need to pass arguments. *)

(*****************************************************************************)
(*                              Binary tree                                  *)
(*****************************************************************************)

(* This type will be used to store efficiently all factors of a given size in a word.
We don't need any label, all that matters is the shape of the tree.
Edges represent bits: 
	* Left child -> 0
	* Right child -> 1
A Leaf symbolizes the end of a valid word, and Nil represents the absence of child (or an empty tree).*)

type 'a tree =
	| Nil (*arbre vide*)
    | Leaf (* end of a factor without son. No need for adding a son since absence of a prefix implies absence of longer factor. *)
    | Node of 'a tree * 'a tree (*left = 0, right = 1*)
;;








let rec print_tree t = match t with
	| Nil -> Printf.printf ""
	| Leaf -> Printf.printf "."
	| Node(t1,t2) -> Printf.printf "Node("; print_tree t1; Printf.printf ","; print_tree t2; Printf.printf ")"
;;

let rec print_elements = function
	| [] -> ()
	| [a] -> print_int a
	| h::t -> print_int h; print_string ";"; print_elements t
;;

let print_list l =		
	print_string "[";
	print_elements l;
	print_string "]\n"
;;

let print_list_as_word l =
	let rec print_elements2 = function
		| [] -> ()
		| h::t -> print_int h; print_elements2 t
	in
	print_elements2 l;
;;

let print_list_of_list l =
	print_string "[";
	let rec print_aux l = match l with
		| [] -> ()
		| [w] -> print_string "["; print_elements w; print_string "]"
		| w1::ww -> print_string "["; print_elements w1; print_string "];\n"; print_aux ww
	in print_aux l;
	print_string "]\n"
;;

let print_array a =
	print_string "[|";
	for i = 0 to Array.length a - 2 do
		print_int a.(i); print_string ";"
	done;
	if Array.length a > 0 then print_int a.(Array.length a -1);
	print_string "|]\n"
;;

let print_array_pos arr start stop =
	(** Prints the factor between start and stop from word "arr". *)
	print_string "[|";
	for i = start to stop do
		print_int arr.(i); print_string ";"
	done;
	print_string "|]"
;;












let rec tree_add t w = match w with
	(** Adds binary word w to binary tree t, where t represents a set of forbidden factors *)
	| [] -> Leaf (* Cut the tree here, whatever comes after. It is enough to check the prefix is absent *)
	| 0 :: ww -> begin match t with
		| Nil -> Node(tree_add Nil ww, Nil) (*adding our factor normally*)
		| Leaf -> Leaf (* Stop here : if we read a leaf, a prefix of the factor we are adding is already in the tree. No need to check for longer factor then. *)
		| Node(t1,t2) -> Node(tree_add t1 ww, t2)
		end
	| 1 :: ww -> begin match t with
		| Nil ->  Node(Nil, tree_add Nil ww)
		| Leaf -> Leaf
		| Node(t1,t2) -> Node(t1, tree_add t2 ww)
		end
	| _ -> raise BadValue
;;
(*Note : we will stock the mirrors of factors in the tree since the words will always be given and constructed reversed.
This does not change anything : it is enough to forbid a suffix of a longer factor.*)


let rec tree_add_arr t word pos = (*TODO*)
	(** Same as tree_add but the word is in a predefined array instead of a list.
	Factor added is the mirror of "word" ending at index "pos". *)
	(*Printf.printf "looking at pos %d of word\n" pos;*)
	if pos = -1 then Leaf (*We are done reading the whole word to get here, or we are adding empty word to tree of suffixes *)
	else match word.(pos) with
	| 0 -> begin match t with
		| Nil -> Node(tree_add_arr Nil word (pos-1), Nil)
		| Leaf -> Leaf (*stop here, factor we are adding already has its prefix in the tree*)
		| Node(t1,t2) -> Node(tree_add_arr t1 word (pos-1), t2)
		end
	| 1 -> begin match t with
		| Nil ->  Node(Nil, tree_add_arr Nil word (pos-1))
		| Leaf -> Leaf
		| Node(t1,t2) -> Node(t1, tree_add_arr t2 word (pos-1))
		end
	| -1 -> raise Empty
	| _ -> raise BadValue
;;

(* Word is a list - version*)
let rec is_in_tree word t =
	(** Checks that "word" does not contain any factor from tree t as a prefix.
	(This check will be made on every letter of a word we build, thus correctly
	forbidding a set of factors in a whole word.) *)
	match word, t with
	| _, Nil -> false (* Cannot contain a forbidden factor from an empty tree. *)
	| _, Leaf -> true (* We end up on a Leaf means that the words contains a prefix that is in the tree. *)
	| [], Node(_,_) -> false (*word did not encounter anything forbidden (yet) *)
	| 0::ww, Node(t1,t2) -> is_in_tree ww t1
	| 1::ww, Node(t1,t2) -> is_in_tree ww t2
	| _, _ -> raise BadValue
;;
(*Note : we will give word in a reversed form, but tree will contain reversed factors. So we still want to check prefixes
(that are actually suffixes).*)


(* CHANGE : WORDS ARE NOW ARRAY. For this one, still need to put suffixes in the tree. *)
let rec is_suffix_in_mirrors_tree word pos t = 
	(** Same as "is_in_tree" but the word is in a predefined array.
	Checks that the mirror of the suffix (ending at pos) is in the tree,
	tree must contain mirrors of forbidden factors. *)
	if pos < 0 then false (*reached the end of word to read, did not find a leaf*)	
	else match t with
	| Nil -> false
	| Leaf -> true (* found a suffix from tree *)	
	| Node(t1,t2) -> match word.(pos) with
		| 0 -> is_suffix_in_mirrors_tree word (pos-1) t1
		| 1 -> is_suffix_in_mirrors_tree word (pos-1) t2
		| -1 -> raise Empty (*means we are reading after end of the word. Problem, not supposed to happen*)
		| _ ->  raise BadValue
;;


let rec has_factor_in_tree word n t =
	(** Checks that "word" has no factor that is also contained (reversed) in tree t. *)
	(*To achieve this, we read letter by letter from the end of the world and check that no suffix is in tree.*)
	let res = ref false in
	let pos = ref n in
	while not(!res) && (!pos) >= 0 do
		if is_suffix_in_mirrors_tree word (!pos) t then
			res := true;
		pos := (!pos) - 1;
	done;
	(!res)
;;

(*****************************************************************************)
(*                              Other tests                                  *)
(*****************************************************************************)

let still_has_no_big_square word n min_period =
	(** Checks that "word" still has no square of period >= p after adding the last letter,
	which is at index n in the array representing the word. *)
	if n < 2*min_period - 1 then true (* cannot have a square of period min_period or more *)
	else begin
		let res = ref true in
		let p = ref min_period in (*checks for squares ending on the last letter, of period p*)
		while !res && (!p) <= (n+1) / 2 do (*p is the tested period, at most half the word if the whole word is a square*)
			let pos = ref (n-(!p)) in
			let still_need_to_test_this_p = ref true in
			while (!still_need_to_test_this_p) && !pos >= n - (2* (!p)) + 1 do
				if word.(!pos) != word.(!pos+(!p)) then
					still_need_to_test_this_p := false (*no square of period p ending on last letter then*)
				else
					pos := !pos - 1		
			done;
			res := not(!still_need_to_test_this_p); (*if this is still true, then we did find a square of period p*)
			p := !p + 1
		done;
		!res
	end
;;

let has_no_big_square word n min_period =
	(** General test checking if "word" has no square of period >= p. (word has length n) *)
	let res = ref true in
	let i = ref 0 in
	while !res && !i <= n do
		if not(still_has_no_big_square word (!i) min_period) then
			res := false;
		i := !i + 1
	done;
	!res
;;


exception Sortir of (int list);; (* This exception is used to interrupt a backtracking when
the result is found, instead of finishing going through every possible word.
Result must be passed as a word. *)

(* word is a list *)
let generate_word forbidden_factors size =
	(** Backtracking that generates a word of size "size" that doesn't contain any factor from tree "forbidden_factors".
	Returns [] if none exists.*)
	let rec gen_aux word =
		(* Stopping case : we generated a word of wanted size*)
		if List.length(word) = size then raise (Sortir word) 
		(* Else : continue backtrack *)
		else begin
			for bit=0 to 1 do
				let new_word = (bit :: word) in
				(*Condition : dodges forbidden factors*)
				if not(is_in_tree new_word forbidden_factors) then
					gen_aux new_word;
			done;
		end
	in try gen_aux [];
	[]
	with Sortir(word) -> List.rev word
;;


(*word is a array*)
let generate_no_big_square forbidden_factors size =
	(** Backtracking that generates a word of size "size" that doesn't contain any factor from tree "forbidden_factors",
	and no square of size at least 3.
	Returns [] if none exists.*)
	let word = Array.make size (-1) in
	let rec aux pos =
		for bit=0 to 1 do
			let new_pos = pos+1 in
			word.(new_pos) <- bit;
			if not(is_suffix_in_mirrors_tree word new_pos forbidden_factors) && (still_has_no_big_square word new_pos 3) then
				if new_pos = (size-1) then raise Sortir0 (*then length is size*)
				else aux new_pos;
			word.(new_pos) <- -1 (*going backward requires to clean end of word*)
		done;
	in try aux (-1);
	[| |]
	with Sortir0 -> word
;;


(*****************************************************************************)
(*                   Searching for forbidden factors                         *)
(*****************************************************************************)

let rec is_forbidden_base word n =
	let res = ref false in
	let pos = ref 0 in
	(*Printf.printf "Looking for word ending at pos %d\n" n;
	print_array word;*)
	while not(!res) && (!pos) < n do (*look for small squares*)
		(*Printf.printf "Testing square at pos %d\n" (!pos);*)
		(*squares of size 1*)
		if word.(!pos) = word.(!pos+1) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+1) (n-(!pos+1)+1)) in
			if not(has_no_big_square reduc_word ((Array.length reduc_word) - 1) 5) then (*-1 since we want position of last letter*)
				res := true; (*In that case we removed one letter at first step and 5 letters at step 2*)
		end;
		(* squares of size 2 *)
		if (!pos) <= (n-3) && word.(!pos) = word.(!pos + 2) && word.(!pos+1) = word.(!pos+3) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+2) (n-(!pos+2)+1)) in
			if not(has_no_big_square reduc_word ((Array.length reduc_word) - 1) 4) then
				res := true; (*In that case we removed 2 letters at first step and 4 letters at step 2*)
		end;
		pos := (!pos) + 1
	done;
	!res
;;


let rec is_forbidden word n forbid_2 forbid_1 =
	(** Checks that no reduction in "word" of a square of size 1 or 2 leads to a forbidden word,
	ie a word containing a factor from corresponding tree of suffix forbid_1 or 2 (corresponding to description below) *)
	let res = ref false in
	let pos = ref 0 in
	while not(!res) && (!pos) < n do (*look for small squares*)
		(*squares of size 1*)
		if word.(!pos) = word.(!pos+1) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+1) (n-(!pos+1)+1)) in
			if has_factor_in_tree reduc_word ((Array.length reduc_word) - 1) forbid_1 then
				res := true
		end;
		(* squares of size 2 *)
		if (!pos) <= (n-3) && word.(!pos) = word.(!pos + 2) && word.(!pos+1) = word.(!pos+3) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+2) (n-(!pos+2)+1)) in
			if has_factor_in_tree reduc_word ((Array.length reduc_word) - 1) forbid_2 then
				res := true
		end;
		pos := (!pos) + 1
	done;
	!res
;;


let rec print_tree t = match t with
	| Nil -> Printf.printf "Nil"
	| Leaf -> Printf.printf "."
	| Node(t1,t2) -> Printf.printf "Node("; print_tree t1; Printf.printf ","; print_tree t2; Printf.printf ")"
;;

let print_array_of_tree a =
	print_string "[|";
	for i = 0 to Array.length a - 2 do
		print_tree a.(i); print_string ";"
	done;
	if Array.length a > 0 then print_tree a.(Array.length a -1);
	print_string "|]\n"
;;

let print_array_of_array_of_tree a =
	print_string "[|\n";
	for i = 0 to Array.length a - 2 do
		print_array_of_tree a.(i); print_string ";"
	done;
	if Array.length a > 0 then print_array_of_tree a.(Array.length a -1);
	print_string "|]\n"
;;




let wrong_factors max_step max_size = (*Generalise 1/3 to any alpha rational -> replace "3" with alpha^-1*)
	let forbidden = Array.make (3*max_step+1) (Array.make (max_step+1) Nil) in
	(*forbidden(r,s) contains all factors in which we can retrieve r letters within s reduction steps --> prog dyn.
	Those will be our forbidden factors : factors that we can reduce efficiently.
	Note : forbidden excludes big squares, this is a separate step of computation*)
	let rec build_forbidden reduc steps =
		(*print_string "beginning build_forbidden\nState of table is :";
		print_array_of_array_of_tree forbidden;*)
		if forbidden.(reduc).(steps) != Nil then forbidden.(reduc).(steps) (*this has already been computed*)
		(*TODO : possible optimisation : no need to remember lines (steps-2) and earlier when we have line (steps-1)*)
		else begin
			(* Base case : check that retrieving any square of size 1 or 2 does not make appear
			a big square in the word (of size 4 or 5) *)
			if steps = 2 then
			begin
				let word = Array.make max_size (-1) in
				let to_forbid = ref Nil in
				let rec find_factors_2 pos =
					for bit=0 to 1 do
						let new_pos = pos+1 in
						word.(new_pos) <- bit;
						(*Printf.printf "beginning of find_factors_2 with pos %d\n" (new_pos);*)
						if not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) (*don't even bother to look at word if it already has a factor in to_forbid*)
						&& (still_has_no_big_square word new_pos 3) then (*don't build a big square, otherwise you're already forbidden by separate case*)
						begin
							(*print_string "entered condition\n";*)
							if is_forbidden_base word new_pos then
								to_forbid := tree_add_arr (!to_forbid) word new_pos 
								(*no need to continue backtracking here, it would have an already forbidden factor as prefix *)
							else if new_pos < (max_size - 1) then (*otherwise length is size max_size, no need to check next letters, limit is reached*)
								find_factors_2 new_pos; (* this word is okay, look for something forbidden later *)
						end;
						word.(new_pos) <- -1 (*going backward requires to clean end of word*)
					done;
				in
				find_factors_2 (-1);
				forbidden.(reduc).(steps) <- (!to_forbid);
				forbidden.(reduc).(steps)
			end
			
			(* Recursive call *)
			else (* expected that steps is at least 3 here, not steps = 1 *)
			begin
				let forbid_2 = build_forbidden (reduc-2) (steps-1) in
				let forbid_1 = build_forbidden (reduc-1) (steps-1) in
				let forbid_3 = build_forbidden (reduc-3) (steps-1) in (*starts from here, want to forbid the previous ones too*)
				(*This way forbidden_factors will contain every factor nicely reducible in any number of steps except just 1 step : separately*)
				let word = Array.make max_size (-1) in
				let to_forbid = ref forbid_3 in
				let rec find_factors pos =
					for bit=0 to 1 do
						let new_pos = pos+1 in
						word.(new_pos) <- bit;
						if not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) (*don't even bother to look at word if it already has a factor in to_forbid*)
						&& (still_has_no_big_square word new_pos 3) then (*don't build a big square, otherwise you're already forbidden by separate case*)
						begin
							if is_forbidden word new_pos forbid_2 forbid_1  then
								to_forbid := tree_add_arr (!to_forbid) word new_pos 
							else if new_pos < (max_size - 1) then (*otherwise length is size max_size, no need to check next letters, limit is reached*)
								find_factors new_pos; (* this word is okay, look for something forbidden later *)
						end;
						word.(new_pos) <- -1 (*going backward requires to clean end of word*)
					done;
				in 
				find_factors (-1);
				forbidden.(reduc).(steps) <- (!to_forbid);
				forbidden.(reduc).(steps) (*returns asked result : a tree of forbidden factors, ie reducing r letters within s steps*)
			end
		end
	in build_forbidden (3*max_step) max_step
;;
		






(*
let rec wrong_factors max_step max_size = (*ici récursivité linéaire terminale à base de construire les facteurs interdits à chaque étape*)
(*TODO*)
(*Adapter pour autoriser un rationnel autre que 1/3 (ici par défaut c'est 1/3 
-> retirer au moins 3 lettres en une étape, ou au moins 6 lettres en deux étapes etc. *)
	if max_step = 2 then begin (*cas de base à 2, car on appelle à "1" qui est le "no big square"*)
		(*TODO : big thing*)
	end
	else begin (*max_step must be at least 3 here, max_step = 1 is for no_big_square, <= 0 makes no sens*)
		let word = Array.make size (-1) in
		let rec build_new_forbidden pos to_forbid = (* returns the tree of all forbidden factors except big squares *)
			...
		
		
		in let forbidden_factors = wrong_factors (max_step - 1) max_size in
		build_new_forbidden (-1) forbidden_factors (* returns the tree of all forbidden factors except big squares *)
	end



let rec wrong_factors max_step max_size =
	(*cas de base*)
	(*TODO*)
	let rec f red steps f_r1_s f_r2_s = 
	(*f(r,s) returns the forbidden factors*)
*)



























(*****************************************************************************)
(*                           Rational Numbers                                *)
(*****************************************************************************)

(* Rational p/q is represented as tuple (p,q). 
This type will be used to keep exact values of rationals throughout the file, instead of floats. *)

type rat = int*int;;


let gt (a:rat) (b:rat) =
	(** Greater Than : Returns the result of comparison a > b *)
	match a,b with
	|(p,q), (p',q') -> (p*q') > (p'*q)
;;

let ge (a:rat) (b:rat) = match a,b with
	(** Greater or Equal : Returns the result of comparison a >= b *)
	|(p,q), (p',q') -> (p*q') >= (p'*q)
;;

let float_of_rat (r:rat) = match r with
	(** Converts rational number to float *)
	|(p,q) -> (float_of_int p)/.(float_of_int q)
;;

let max_rat (r1:rat) (r2:rat) = 
	(** Returns max(r1,r2) *)
	if ge r1 r2 then r1 else r2
;;

let rat_minus (r1 : rat) (r2:rat) = match r1,r2 with
	(** Returns r1 - r2 *)
	|(p,q), (p',q') -> (p*q'-p'*q, q*q')
;;

let inter (r1 : rat) (r2:rat) = match r1, r2 with
	(** Returns an intermediate rational number between r1 and r2
	(for a dichotomy). *)
	|(p,q), (p',q') -> (p+p', q+q')
;;



(*****************************************************************************)
(*                                Words                                      *)
(*****************************************************************************)

(* Word will be represented in two different ways depending on what we want to do with them :
- A list of ints 0 or 1. This is the most common way. 
	Warning : Since letters are added on the fly, the word is reversed in the list.
- An array of ints 0 or 1. Useful for some backtracking where we need to test alpha-freeness very often.

We thus need functions to manipulate them both as a list and an array. *)

exception TooShortList;; (* This exception means that the word given in argument was too short.
This usually means a factor of wrong size was given, ie size different that "d". *)
exception NonMatchingSize;; (* Similar to TooShortList in more general. 
Indicates that the size of the word and the size of the tree that were given in argument don't match*)


let rec isolate_factor word d =
	(** Returns the prefix of "word" of size d*)
	if d = 0 then [] else match word with
	| [] -> raise TooShortList
	| h :: t -> h :: (isolate_factor t (d-1))
;;


(* ---------- Thue-Morse Words ---------- *)

let thue_morse n =
	(** Generates the word of Thue-Morse of size n. *)
	let res = Array.make (n+1) (-1) in
	res.(0) <- 0;
	for i = 1 to n do
		let k = (i mod 2) in 
		if k = 0 then res.(i) <- res.(i/2)
		else res.(i) <- 1 - (res.(i/2))
	done;
	res
;;


let ternaire_sans_carre n =
	(** Generates a ternary sequence of Thue-Morse of size at least n. 
	This uses the "counting the number of 1s between 0s" method.*)
	let t_m = thue_morse (4*n) in (*I take some margin on the size.*)
	(*At most 4 letters in the binary word will give one letter in the ternary word.*)
	let res = Array.make n (-1) in
	let i = ref 1 in
	let i_res = ref 0 in
	while !i_res < n do
		let current_chain_of_1 = ref 0 in
		while t_m.(!i) = 1 do
			current_chain_of_1 := !current_chain_of_1 + 1;
			i := !i+1
		done;
		i := !i+1;
		res.(!i_res) <- !current_chain_of_1;
		i_res := !i_res + 1;
	done;
	res
;;

let hom_transform phi n =
	(** Generates the binary word obtained by applying morphism phi
	on the square-free ternary word of Thue Morse. *)
	let ternaire = ternaire_sans_carre n in
	List.concat (List.map phi (Array.to_list ternaire))
;;

let hom_image phi l word =
	let word_to_convert = (Array.to_list (Array.sub word 0 l)) in
	List.concat (List.map phi word_to_convert)
;;



