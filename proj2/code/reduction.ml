
(*****************************************************************************)
(*                              Exceptions                                   *)
(*****************************************************************************)

exception BadValue;; (* This exception means that something else than a bit 0 or 1 was read. *)
exception Empty;; (* This means a word (as a predefined array of -1) lacks a letter at an observed position. *)
exception Sortir;; (* This is raised to end a backtrack when a satisfying object is constructed. *)



(*****************************************************************************)
(*                           Rational Numbers                                *)
(*****************************************************************************)

(* Rational p/q is represented as tuple (p,q). 
This type will be used to keep exact values of rationals throughout the file, instead of floats.
Used to compute S_alpha, the set of forbidden factors when allowing reductions of size at most f(n)/n = alpha. *)

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

let rat_ceil (r : rat) = match r with
	(** Returns the ceil of rational r *)
	|(p,q) -> let test = (p/q)*q in
		if test = p then p/q else p/q + 1
;;

let rat_inv (r : rat) = match r with
	(** Returns the inverse of rational r *)
	|(p,q) -> (q,p)
;;


(*****************************************************************************)
(*                             Binary trees                                  *)
(*****************************************************************************)

(* This type will be used to store efficiently all factors forbidden in a word as suffixes.
We don't need any label, all that matters is the shape of the tree.
Edges represent bits: 
	* Left child -> 0
	* Right child -> 1
A Leaf symbolizes the end of a factor, and Nil represents the absence of child (or an empty tree).*)

type 'a tree =
	| Nil (* empty tree *)
    | Leaf (* end of a factor without son. No need for adding a son since absence of a prefix implies absence of longer factor. *)
    | Node of 'a tree * 'a tree (*left = 0, right = 1*)
;;

(*Note : we will stock the mirrors of factors in the tree since the words will always be given and constructed from the end.*)

let rec tree_add t word n is_mirror = (*TODO*)
	(** Adds mirror of prefix from array "word" ending at position "n".*)
	let rec aux t word pos n is_mirror =
		if pos = -1 then Leaf (*We are done reading the whole word to get here, or we are adding empty word to tree of suffixes *)
		else let current_index = if is_mirror then pos else (n-pos) in
		match word.(current_index) with
		| 0 -> begin match t with
			| Nil -> Node(aux Nil word (pos-1) n is_mirror, Nil)
			| Leaf -> Leaf (*stop here, factor we are adding already has its prefix in the tree*)
			| Node(t1,t2) -> Node(aux t1 word (pos-1) n is_mirror, t2)
			end
		| 1 -> begin match t with
			| Nil ->  Node(Nil, aux Nil word (pos-1) n is_mirror)
			| Leaf -> Leaf
			| Node(t1,t2) -> Node(t1, aux t2 word (pos-1) n is_mirror)
			end
		| -1 -> raise Empty
		| _ -> raise BadValue
	in aux t word n n is_mirror
;;

let rec is_suffix_in_mirrors_tree word pos t = 
	(** Checks that the mirror of a suffix (ending at index "pos") is in the tree.
	Tree must contain mirrors of forbidden suffixes. *)
	if pos < 0 then (t=Leaf) (*reached the end of word to read, true only if find a leaf*)	
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

let rec nb_of_factors_in_tree t = match t with
	| Nil -> 0
	| Leaf -> 1
	| Node(t1,t2) -> nb_of_factors_in_tree t1 + nb_of_factors_in_tree t2
;;

let rec tree_to_list_of_factors t =
	let rec aux t word = match t with
		| Nil -> []
		| Leaf -> [List.rev word] (* for lexicographical order, since tree contains every mirror too *)
		| Node(t1,t2) -> (aux t1 (0::word))@(aux t2 (1::word))
	in aux t []
;;


(*****************************************************************************)
(*                           Square detection                                *)
(*****************************************************************************)

let still_has_no_big_square word n min_period =
	(** Checks that "word" still has no square of period >= min_period after adding the last letter,
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


(*****************************************************************************)
(*                    Part I : Verification of a set                         *)
(*****************************************************************************)

(*word is a array*)
let generate forbidden_factors size alpha = 
	(** Backtracking that generates a word of size "size" that doesn't contain any factor from tree "forbidden_factors",
	and no square of size at least 1/alpha.
	Returns [||] if none exists.*)
	let min_period = rat_ceil (rat_inv alpha) in
	let word = Array.make size (-1) in
	let rec aux pos =
		for bit=0 to 1 do
			let new_pos = pos+1 in
			word.(new_pos) <- bit;
			if not(is_suffix_in_mirrors_tree word new_pos forbidden_factors) && (still_has_no_big_square word new_pos min_period) then
				if new_pos = (size-1) then raise Sortir (*then length is size*)
				else aux new_pos;
			word.(new_pos) <- -1 (*going backward requires to clean end of word*)
		done;
	in try aux (-1);
	[| |]
	with Sortir -> word
;;
(*alpha is what we're trying to prove as bound, formerly 1/3.
If alpha = p/q, we forbid all factors that allow us to remove at least q/p letters in 1 step,
and k.q/p letters in k steps*)


(*****************************************************************************)
(*                   Searching for forbidden factors                         *)
(*****************************************************************************)

let rec is_forbidden_base word n reduc =
	let res = ref false in
	let pos = ref 0 in
	while not(!res) && (!pos) < n do (*look for small squares*)
		if word.(!pos) = word.(!pos+1) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+1) (n-(!pos+1)+1)) in
			if not(has_no_big_square reduc_word ((Array.length reduc_word) - 1) (reduc-1)) then (*-1 since we want position of last letter*)
				res := true; (*In that case we removed one letter at first step and 5 letters at step 2 for example*)
		end;
		(* squares of size 2 *)
		if (!pos) <= (n-3) && word.(!pos) = word.(!pos + 2) && word.(!pos+1) = word.(!pos+3) then begin
			let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+2) (n-(!pos+2)+1)) in
			if not(has_no_big_square reduc_word ((Array.length reduc_word) - 1) (reduc-2)) then
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



(* Debugging function : prints the cases of the table that were computed.
let print_empty a = 
	for i = 0 to Array.length(a)-1 do
		for j = 0 to Array.length(a.(0))-1 do
			if a.(i).(j) = Nil then print_string "o"
			else print_string "x";
		done;
		print_string "\n";
	done
;;
*)

let wrong_factors max_step max_size = (*Generalise 1/3 to any alpha rational -> replace "3" with alpha^-1*)
	let forbidden = Array.make_matrix (3*max_step+1) (max_step+1) Nil in
	(*forbidden(r,s) contains all factors in which we can retrieve r-3l letters within s-l reduction steps,
	for 0 <= l <= max(s-1, r/3) --> prog dyn.
	Those will be our forbidden factors : factors that we can reduce efficiently.
	Note : forbidden excludes big squares, this is a separate step of computation*)
	let rec build_forbidden reduc steps =
		if forbidden.(reduc).(steps) != Nil then forbidden.(reduc).(steps) (*this has already been computed*)
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
						if not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) (*don't even bother to look at word if it already has a factor in to_forbid*)
						&& (still_has_no_big_square word new_pos reduc) then (*don't build a big square, otherwise you can remove "reduce" letters in one step only*)
						begin
							if is_forbidden_base word new_pos reduc then
							begin
								to_forbid := tree_add (!to_forbid) word new_pos true;
								(*no need to continue backtracking here, it would have an already forbidden factor as prefix *)
								to_forbid := tree_add (!to_forbid) word new_pos false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
							end
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
				let forbid_3 = build_forbidden (reduc-3) (steps-1) in (*starts from here, want to forbid the previous ones too*)
				let forbid_2 = build_forbidden (reduc-2) (steps-1) in
				let forbid_1 = build_forbidden (reduc-1) (steps-1) in
				
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
							begin
								to_forbid := tree_add (!to_forbid) word new_pos true;
								(*no need to continue backtracking here, it would have an already forbidden factor as prefix *)
								to_forbid := tree_add (!to_forbid) word new_pos false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
							end
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





