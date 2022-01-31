
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

let rat_floor (r : rat) = match r with
	(** Returns the floor of rational r *)
	| (p,q) -> p/q
;;

let rat_inv (r : rat) = match r with
	(** Returns the inverse of rational r *)
	|(p,q) -> (q,p)
;;

let mult_by_int (r : rat) n = match r with
	(** Multiply rational r by integer n *)
	| (p,q) -> (n*p,q)
;;

(*****************************************************************************)
(*                    Words and diverse functions                            *)
(*****************************************************************************)

let complement word =
	(** Turns a word into its binary complement. 0 -> 1 and 1 -> 0. *)
	let res = Array.make (Array.length word) 0 in
	for i = 0 to (Array.length word - 1) do
		res.(i) <- 1-word.(i)
	done;
	res
;;

let is_greater_than_reverse word n = (* If it is the case, no need to test. --> already done for its reverse. *)
	(** Checks if a word is lexicographically greater than its reverse.
	"word" is an array, index of last bit is n. *)
	let rec aux pos =
		if pos > n then false (*they are equal, so word is not strictly greater than its reverse*)
		else begin
			if word.(pos) > word.(n-pos) then true
			else if word.(pos) < word.(n-pos) then false
			else aux (pos+1)
		end
	in aux 0
;;

let rec power x n = 
	(** Computes x^n in a simple recursive way, not optimal (no need) *)
	if n = 0 then 1 
	else x * (power x (n-1))
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

type status_type = NotPrefix | StrictPrefix | InTree | HasPrefix ;; 
(* Used to compare a word and a tree of prefix(/suffix). *)

let prefix_of_factor_in_tree tt word n =
	(** Determines if the word has a prefix in a prefix tree, or is a prefix of a factor in the tree,
	or is exactly in the tree or not at all. *)
	let rec aux t pos =
		if pos > n then match t with
			| Nil -> NotPrefix
			| Leaf -> InTree
			| _ -> StrictPrefix
		else match t with
		| Nil -> NotPrefix
		| Leaf -> HasPrefix (*already seen a prefix from tree but word is longer.*)
		| Node(t1,t2) -> match word.(pos) with
			| 0 -> aux t1 (pos+1)
			| 1 -> aux t2 (pos+1)
			| -1 -> raise Empty (*means we are reading after end of the word. Problem, not supposed to happen*)
			| _ ->  raise BadValue
	in aux tt 0
;;

(*Note : we will stock the mirrors of factors in the tree since the words will always be given and constructed from the end.*)

let rec tree_add t word n is_mirror = (*EDIT : does not add words that have any factor in tree*)
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

let rec union t1 t2 = match t1,t2 with
	(** Returns the union of prefix trees t1 and t2, which is a prefix tree containing all factors from both *)
	| Nil, t2 -> t2
	| t1, Nil -> t1
	| Leaf, t2 -> Leaf (*cut other tree, its word have this one as prefix*)
	| t1, Leaf -> Leaf
	| Node(t11, t12), Node(t21,t22) -> Node(union t11 t21, union t12 t22)
;;

let rec nb_of_factors_in_tree t = match t with
	(** Counts the number of words in the tree.
	Used for statistical purposes only. *)
	| Nil -> 0
	| Leaf -> 1
	| Node(t1,t2) -> nb_of_factors_in_tree t1 + nb_of_factors_in_tree t2
;;

let rec tree_to_list_of_factors t =
	(** Converts a tree into a list of words (lists).
	Used for printing and putting in files. *)
	let rec aux t word = match t with
		| Nil -> []
		| Leaf -> [List.rev word] (* for lexicographical order, since tree contains every mirror too *)
		| Node(t1,t2) -> (aux t1 (0::word))@(aux t2 (1::word))
	in aux t []
;;


(*****************************************************************************)
(*                           File manipulation                               *)
(*****************************************************************************)


let write_factors l file = (*l is a list of factor*)
	(** Fill the file "file" with the words contained in list l (each word is a list).
	Writes one word per line, as a string of "0" and "1". *)
	let oc = open_out file in (* create or truncate file, return channel *)
	let rec aux_write ll = match ll with
		| [] -> ()
		| h::t -> let str = String.concat "" (List.map string_of_int h) in 
			Printf.fprintf oc "%s\n" str; aux_write t
	in aux_write l;
	close_out oc
;;

let write_tree_to_file tree file =
	(** Same as write_factors but takes a tree as input. *)
	let l = tree_to_list_of_factors tree in
	write_factors l file
;;

let get_tree_from_file file =
	(** Reads a file containing one word per line (as a bit string) and creates a tree
	containing them. *)
	let res = ref Nil in
	let in_channel = open_in file in
	try
	  while true do
		let line = input_line in_channel in
		let factor = Array.init (String.length line) (fun i -> (int_of_char line.[i]) - 48) in (*ASCII code for '0' is 48*)
		res := tree_add (!res) factor (Array.length factor - 1) false
	  done;
	  (!res)
	with End_of_file ->
	  close_in in_channel; (!res)
;;

let exists_file file =
	(** Tests if a file with the name "file" exists.
	I just recoded Sys.file_exists without knowing it... *)
	try
		let in_channel = open_in file in
		close_in in_channel;
		true
	with Sys_error s -> false
;;

(* Note : from now on, we will work on files representing the cases of the prog dyn table.
Each case (i,j) = (reduc, steps) contains the tree of factors from which we can remove at least "reduc" letters in "steps" steps.
The name of a file representing such a case is "tree_files_p_q/f_reduc_steps_size.txt" where :
	p/q = alpha is the bound we try to achieve. dir_name = "tree_files_p_q/".
	x = reduc (number of letters to be removed by reduction)
	y = steps (number of reduction steps allowed to remove letters)
	z = maximal size of factors searched. *)

let exists_between reduc steps min max dir_name =
	(** Tests the existence of a file of name "tree_files_p_q/f_x_y_z.txt" with z included between min and max *)
	let res = ref 0 in
	let index = ref min in
	let file_name_prefix = (dir_name^"/f_"^(string_of_int reduc)^"_"^(string_of_int steps)^"_") in
	while (!res) = 0 && (!index) <= max do
		if exists_file (file_name_prefix^(string_of_int (!index))^".txt") then
			res := (!index);
		incr index;
	done;
	(!res)
;;

let get_case_below reduc steps tot_letter max_size dir_name =
	(** Looks for a file containing the case (r, steps) of the prog dyn table where
	r is greater than "reduc", i.e. the tree of factors from which we can remove more letters than required. *)
	let file_name_prefix = (dir_name^"/f_") in
	let name_inter = ("_"^(string_of_int steps)^"_") in
	let r = ref (reduc + 1) in
	let found_case = ref false in
	let tree = ref Nil in
	while not(!found_case) && (!r) <= tot_letter do
		let size_exist = (exists_between (!r) steps max_size 50 dir_name) in
		if size_exist != 0 then begin
			found_case := true;
			tree := get_tree_from_file (file_name_prefix^(string_of_int (!r))^name_inter^(string_of_int size_exist)^".txt")
		end
		else incr r
	done;
	(!tree)
;;

let get_case_above reduc steps max_size dir_name =
	(** Looks for a file containing the case (r, steps) of the prog dyn table where
	r is lower than "reduc", i.e. the tree of factors from which we can remove less letters than required. *)
	let file_name_prefix = (dir_name^"/f_") in
	let name_inter = ("_"^(string_of_int steps)^"_") in
	let r = ref (reduc - 1) in
	let found_case = ref false in
	let tree = ref Nil in
	while not(!found_case) && (!r) > 0 do
		let size_exist = (exists_between (!r) steps max_size 50 dir_name) in
		if size_exist != 0 then begin
			found_case := true;
			tree := get_tree_from_file (file_name_prefix^(string_of_int (!r))^name_inter^(string_of_int size_exist)^".txt")
		end
		else decr r
	done;
	(!tree)
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
			res := not(!still_need_to_test_this_p); (*if still_need is still true by now, then we did find a square of period p*)
			p := !p + 1
		done;
		!res
	end
;;

let smallest_suffix_square_above_period word n min_period =
	(** Checks that "word" still has no square of period >= min_period after adding the last letter,
	which is at index n in the array representing the word. 
	If it has on, it returns the array containing the square,
	otherwise it returns [||]*)
	if n < 2*min_period - 1 then [||] (* cannot have a square of period min_period or more *)
	else begin
		let no_square = ref true in
		let p = ref min_period in (*checks for squares ending on the last letter, of period p*)
		while !no_square && (!p) <= (n+1) / 2 do (*p is the tested period, at most half the word if the whole word is a square*)
			let pos = ref (n-(!p)) in
			let still_need_to_test_this_p = ref true in
			while (!still_need_to_test_this_p) && !pos >= n - (2* (!p)) + 1 do
				if word.(!pos) != word.(!pos+(!p)) then
					still_need_to_test_this_p := false (*no square of period p ending on last letter then*)
				else
					pos := !pos - 1		
			done;
			no_square := not(!still_need_to_test_this_p); (*if still_need is still true, then we did find a square of period p*)
			if !no_square then 	p := !p + 1
		done;
		if !no_square then [||] else Array.sub word (n-2*(!p)+1) (2*(!p))
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
(*             Verification Part : Dodging a set of factors                  *)
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
(*alpha is what we're trying to prove as bound, for example 1/3.
If alpha = p/q, we forbid all factors that allow us to remove at least q/p letters in 1 step,
and k.q/p letters in k steps. For factors forbidden in at least 2 steps, they are given in tree "forbidden_factors".*)


(*****************************************************************************)
(*                  Building forbidden factors Part                          *)
(*****************************************************************************)


(*Debugging function, ignore this.*)
let print_empty a = 
	(** Prints the cases of the table that were computed (non empty). *)
	for i = 0 to Array.length(a)-1 do
		for j = 0 to Array.length(a.(0))-1 do
			if a.(i).(j) = Nil then print_string "o"
			else print_string "x";
		done;
		print_string "\n";
	done
;;


let wrong_factors max_step max_sizes alpha_inv =
	(** MAIN FUNCTION !
	Generates a tree of forbidden factors to prove a bound of "alpha_inv", that is every factor from which
	we can remove k.q/p factors in k steps for some k, where alpha_inv = p/q.
	Warning : Contains important subfunctions ! *)
	let alpha = rat_inv (alpha_inv) in (*when given bound p/q, we'd rather work with ratio q/p.*)
	let tot_letters = (rat_ceil (mult_by_int alpha max_step)) in (*number of letters to remove in total : k.q/p as explained before.*)
	let forbidden = Array.make_matrix (tot_letters+1) (max_step+1) Nil in (*the prog dyn table, cf Readme for explanation.*)
	let dir_name = match alpha_inv with (*name of directory in which to put the results.*)
		| (p,q) -> "tree_files_"^ (string_of_int p)^"_"^(string_of_int q)
	in
	
	let rec build_forbidden reduc steps max_size =
		(** The recursive function for filling in the case (reduc,steps) of the prog dyn table. Main skeleton of the program. *)
		
		(********************************************************************************)
		(* Case (reduc, steps) already computed and filled in this run of the algorithm.*)
		if forbidden.(reduc).(steps) != Nil then forbidden.(reduc).(steps)
		
		(*********************************************************************************************************)
		(* Case (reduc, steps) empty but a file exists with the result tree for an equal or greater size of factor.
		Then fill it with this tree without further computation.*)
		else let file_name_prefix = (dir_name^"/f_"^(string_of_int reduc)^"_"^(string_of_int steps)^"_") in
		let size_exist = (exists_between reduc steps max_size 50 dir_name) in (*Warning : 50 hardcoded as maximal possible size of factors*)
		if size_exist != 0 then begin
			let forbid = get_tree_from_file (file_name_prefix^(string_of_int size_exist)^".txt") in
			forbidden.(reduc).(steps) <- forbid;
			forbidden.(reduc).(steps)
		end
		
		(******************************************************)
		(* Case (reduc, steps) empty and needs to be computed.*)
		else begin
			let to_forbid = ref (get_case_below reduc steps tot_letters max_size dir_name) in 
			(*Start from factors in which we remove more letters, if they exists. Those will still be forbidden here, or a prefix of them.*)

			(*If the case (reduc, steps) was already computed but for smaller factors, use them, they are still forbidden.
			Moreover, words of size smaller than them have already been tested -> go faster.*)
			let threshold = ref 0 in 
			let size_exist = (exists_between reduc steps 1 max_size dir_name) in
			if size_exist != 0 then begin
				let forbid_less = get_tree_from_file (file_name_prefix^(string_of_int size_exist)^".txt") in
				to_forbid := union (!to_forbid) forbid_less;
				threshold := size_exist;
			end;
			
			(* If we make at least 3 steps of reduction, we can also start from a case from previous column of the table. 
			See Readme for explanation of inclusions. *)
			let floor_min_period = rat_floor alpha in
			if steps > 2 then
				to_forbid := union (!to_forbid) (build_forbidden (reduc - floor_min_period) (steps-1) max_size);


			let tree_above = get_case_above reduc steps max_size dir_name in
			let min_pertinent = rat_ceil (mult_by_int (power 2 steps - 1, power 2 steps) reduc) in (* Cannot retrieve more than half the letters at each step *)
			let word = Array.make max_size (-1) in
			
			let rec find_factors pos to_test_previous =
				(** Backtrack to build and find the factors that are forbidden (can remove "reduc" letters in "steps" steps).
				Uses a number of optimisations. See Readme for more explanation. *)
				for bit=0 to 1 do
					let new_pos = pos+1 in
					word.(new_pos) <- bit;
					
					if word.(0) = 0 && not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) then
					begin
						if tree_above != Nil && not(to_test_previous) then begin
							let status_prefix = prefix_of_factor_in_tree tree_above word new_pos in (* NotPrefix | StrictPrefix | InTree *)
							(*Note : tree is symmetric, so it is both a prefix and suffix tree.*)
							begin match status_prefix with
							| NotPrefix -> () (*cannot remove even less letters, no need to test for more letters. Stop backtrack *) 
							| StrictPrefix -> if new_pos < (max_size - 1) then
									find_factors new_pos false (*still don't need to test right now, will need later*)
							| InTree -> (*from now on need to test the word*)
								if new_pos >= min_pertinent && new_pos >= (!threshold) && not(is_greater_than_reverse word new_pos) &&
								(not(still_has_no_big_square word new_pos (reduc-1)) (*tested separately from is_forbidden for speedup*)
								|| is_forbidden word new_pos reduc steps max_size) then begin (*forbidden word by one step of reduc*)
									to_forbid := tree_add (!to_forbid) word new_pos true;
									to_forbid := tree_add (!to_forbid) word new_pos false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
									to_forbid := tree_add (!to_forbid) (complement word) new_pos true; (*complement of word is also forbidden*)
									to_forbid := tree_add (!to_forbid) (complement word) new_pos false;
								end
								else if new_pos < (max_size - 1) then
									find_factors new_pos true
							| HasPrefix -> raise BadValue
							end;
						end
						else if new_pos >= min_pertinent && (*don't test if no need*)
						new_pos >= (!threshold) && not(is_greater_than_reverse word new_pos) && (*exclude already tested factors*)
						(not(still_has_no_big_square word new_pos (reduc-1)) (*tested separately (in 1 step) from is_forbidden for speedup*)
						|| is_forbidden word new_pos reduc steps max_size) then begin
							to_forbid := tree_add (!to_forbid) word new_pos true;
							to_forbid := tree_add (!to_forbid) word new_pos false; (*forbid mirror of factor*)
							to_forbid := tree_add (!to_forbid) (complement word) new_pos true; (*forbid complement of factor*)
							to_forbid := tree_add (!to_forbid) (complement word) new_pos false; (*forbid mirror of complement of factor*)
						end
						else if new_pos < (max_size - 1) then (*otherwise max size of factor is reached*)
						begin
							find_factors new_pos true; (* this word is okay, look for something forbidden later *)
						end
					end;
					word.(new_pos) <- -1 (*going backward : clean end of word*)
				done;
			in
			find_factors (-1) false;

			forbidden.(reduc).(steps) <- (!to_forbid);
			Printf.printf "--> Done computing factors of size at most %d from which we remove %d letters in %d steps%!\n" max_size reduc steps;
			
			(****************************************************************************)
			(* Writing result of previous backtrack in appropriate file, if not too big.*)
			try
				write_tree_to_file forbidden.(reduc).(steps) (file_name_prefix^(string_of_int max_size)^".txt");
				Printf.printf "----> Wrote corresponding tree in a file\n%!";
				let size_exist = (exists_between reduc steps 1 (max_size-1) dir_name) in (* this checks if a file existed with smaller factor size *)
				if size_exist != 0 then
					Sys.remove (file_name_prefix^(string_of_int size_exist)^".txt");
					(*Delete previous file if factors were computed with a bigger size, only keep the better (bigger) tree *)
				forbidden.(reduc).(steps)
			with Stack_overflow -> (Printf.printf "Warning : could not put result in a file (too big : Stack_overflow)\n%!";
			forbidden.(reduc).(steps));
		end
	
	and is_forbidden word n reduc steps max_size =
		(** Checks that a word is forbidden, 
		i.e. there is a reduction of a square in "word" that leads to a forbidden word with less steps of reduction. *)
		(*Beginning is similar to "still_has_no_big_square".*)
		let res = ref false in
		let pos = ref 0 in
		let max_period = (reduc - 1)in
		while not(!res) && (!pos) < n do (*look for small squares beginning at pos, no use to check last letter*)
			let period = ref 1 in
			while not(!res) && (!period) <= max_period do
				let is_square = ref true in
				if (!pos + 2*(!period)-1) > n then is_square := false;
				let pos_square = ref 0 in
				while !is_square && pos_square < period do (* check we have a square of size period at pos "pos" *)
					if word.(!pos + (!pos_square)) != word.(!pos + (!period) + (!pos_square)) then
						is_square := false;
					pos_square := !pos_square + 1;
				done;
				
				(*******************************************************************************)
				(* A square was found, try to make reduction and check forbidden in less steps.*)
				if (!is_square) then begin
					if reduc - (!period) <= 2*(steps-1) then begin
						res := true (*we are sure to be able to remove at least 2 letters by step left (by prolonging word if needed) --> forbidden *)
					end
					else begin
						let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+(!period)) (n-(!pos+(!period))+1)) in
						if steps = 2 then res := not(has_no_big_square reduc_word ((Array.length reduc_word) - 1) (reduc - (!period))) (*cas de base*)
						else begin
							let previous_forbidden = (build_forbidden (reduc - (!period)) (steps-1) (max_size-1)) in 
							res := (has_factor_in_tree reduc_word ((Array.length reduc_word) - 1) previous_forbidden)
						end
					end
				end;
				incr period;
			done;
			pos := (!pos + 1)
		done;
		!res
	in 
	
	(************************************************************************************************)
	(* Now the useful forbidden factors are the cases that are tightly above k.q/p, where alpha = p/q.
	Add them one by one.*)
	let res = ref Nil in
	let enough = ref false in
	let nb_steps = ref 2 in
	while not(!enough) && (!nb_steps) <= max_step do
		let tight_tree = build_forbidden (rat_ceil (mult_by_int alpha (!nb_steps))) (!nb_steps) (max_sizes.(!nb_steps)) in
		res := union (!res) tight_tree;
		Printf.printf "Added factors forbidden in %d steps of size at most %d\n%!" (!nb_steps) max_sizes.(!nb_steps);
		Printf.printf "We forbid %d factors in total\n%!" (nb_of_factors_in_tree (!res));
		let dodging = (generate (!res) 1000 alpha_inv) in
		if dodging = [||] then begin
			enough := true;
			Printf.printf "We cannot build an infinite word dodging all these factors, after %d steps !\n" (!nb_steps);
		end;
		incr nb_steps;
	done;
	(*print_empty (forbidden);*)
	(!res)
;;

















(*****************************************************************************)
(*                Dead code : dead ends and previous tests                   *)
(*****************************************************************************)

exception Found of int*int;;
let rec reduce_ratio word n alpha_inv nb_letters_removed nb_steps_done =  
	(*Printf.printf "Checking number of steps giving max ratio for (%d,%d)\non word :" nb_letters_removed nb_steps_done;
	print_array word;*)
	let alpha = rat_inv alpha_inv in
	let res_nb_letters = ref nb_letters_removed in
	let res_nb_steps = ref (max nb_steps_done 1) in
	let max_period = rat_ceil (rat_minus (mult_by_int alpha (nb_steps_done + 1)) (nb_letters_removed, 1)) in
	(*Printf.printf "max period is %d\n" max_period;*)
	(*max_period is period to check in reduction, if we have a square bigger than that it's ok !*)
	if not(has_no_big_square word n max_period) then
	begin
		Printf.printf "\n We had removed %d letters in %d steps and found a square of size %d in the word : \n" nb_letters_removed nb_steps_done max_period;
		raise (Found (nb_letters_removed + max_period, nb_steps_done + 1)); (*this does makes i letters removed in j steps such that i/j >= alpha.*)
	end;
	let pos = ref 0 in
	while (!pos) < n do (*look for small squares beginning at pos, no use to check last letter*)
		let period = ref 1 in
		while (!period) <= max_period do
			let is_square = ref true in
			if (!pos + 2*(!period)-1) > n then is_square := false;
			(*else Printf.printf "checking squares of size %d beginning at pos %d\n" (!period) (!pos);*)
			let pos_square = ref 0 in
			while !is_square && pos_square < period do (* check we have a square of size period at pos "pos" *)
				if word.(!pos + (!pos_square)) != word.(!pos + (!period) + (!pos_square)) then
					is_square := false;
				pos_square := !pos_square + 1;
			done;
			if (!is_square) then begin
				if gt (!period+nb_letters_removed, 1+nb_steps_done) (!res_nb_letters, !res_nb_steps) then begin
					res_nb_letters := !period + nb_letters_removed;
					res_nb_steps := 1 + nb_steps_done;
				end;
				let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+(!period)) (n-(!pos+(!period))+1)) in
				let (nb_letters, nb_steps) = reduce_ratio reduc_word ((Array.length reduc_word) - 1) 
					alpha_inv (nb_letters_removed + (!period)) (nb_steps_done + 1) in
				if ge (nb_letters+(!period), nb_steps + 1) alpha then raise (Found (nb_letters + (!period), nb_steps + 1)); (*we have a chain such that i/j >= alpha. Not supposed to get there, 
				Found should be raise earlier when stumbling upon a big square at some point (last step).*)
				if gt (nb_letters+(!period), nb_steps+1) (!res_nb_letters, !res_nb_steps) then begin
					res_nb_letters := nb_letters+(!period);
					res_nb_steps := nb_steps+1;
				end;
			end;
			period := !period + 1;
		done;
		pos := (!pos + 1)
	done;
	(*Printf.printf "End of call on word :";
	print_array word;
	Printf.printf "Result is (%d,%d)\n" (!res_nb_letters) (!res_nb_steps);*)
	(!res_nb_letters, !res_nb_steps)
;;


(* Pré-traitement *)
			(* Only test each of those factors once to see if they're still forbidden. Our new to_forbid is included in it. *)
			(*let rec span_tree t factor = match t with
				| Nil -> ()
				| Leaf -> let factor_arr = (Array.of_list factor) in
					let n = (List.length factor-1) in
					if (n+1) <= max_size then begin (*else bigger factor than we are considering*)
						(*Printf.printf "2.putting factor below of length %d in word under it of length %d \n" (n+1) max_size;
						print_array factor_arr;
						print_array word;*)
						Array.blit factor_arr 0 word 0 (n+1);
						(*Printf.printf "Replacement done ok.\n";*)
						if not(is_suffix_in_mirrors_tree word n (!to_forbid)) then begin
							if (not(still_has_no_big_square word n (reduc-1)) (*tested separately from is_forbidden for speedup*)
							|| is_forbidden word n reduc steps max_size) then
							begin
								to_forbid := tree_add (!to_forbid) word n true;
								to_forbid := tree_add (!to_forbid) word n false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
								to_forbid := tree_add (!to_forbid) (complement word) n true; (*complement of word is also forbidden*)
								to_forbid := tree_add (!to_forbid) (complement word) n false;
							end
							(*else if (n+1) < max_size then begin
								let verbose = ref false in
								if factor_arr = [|1;0;0;1;1;0;0;0;1|] then
								begin
									Printf.printf "We backtrack from good candidate !\n";
									Printf.printf "backtracking from position %d\n" (n+1);
									Printf.printf "Beginning of word in backtrack will be :\n";
									print_array word;
									verbose := true
								end;
								find_factors n (!verbose);
								Array.fill word 0 max_size (-1);
							end*)
						end
					end
				| Node(t1,t2) -> (span_tree t1 (0::factor)); (span_tree t2 (1::factor))
				
				*)
			(* False good idea : cannot append prefixes from factor in tree, and we don't want to store all prefix ^ bad factor*)

