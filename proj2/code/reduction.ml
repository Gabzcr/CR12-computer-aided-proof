
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
	| (p,q) -> p/q
;;

let rat_inv (r : rat) = match r with
	(** Returns the inverse of rational r *)
	|(p,q) -> (q,p)
;;

let mult_by_int (r : rat) n = match r with
	| (p,q) -> (n*p,q)
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
	| Nil, t2 -> t2
	| t1, Nil -> t1
	| Leaf, t2 -> Leaf (*cut other tree, its word have this one as prefix*)
	| t1, Leaf -> Leaf
	| Node(t11, t12), Node(t21,t22) -> Node(union t11 t21, union t12 t22)
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
(*                           File manipulation                               *)
(*****************************************************************************)


let write_factors l file = (*l is a list of factor*)
	let oc = open_out file in (* create or truncate file, return channel *)
	let rec aux_write ll = match ll with
		| [] -> ()
		| h::t -> let str = String.concat "" (List.map string_of_int h) in 
			Printf.fprintf oc "%s\n" str; aux_write t
	in aux_write l;
	close_out oc
;;

let write_tree_to_file tree file =
	let l = tree_to_list_of_factors tree in
	write_factors l file
;;

let get_tree_from_file file =
	let res = ref Nil in
	let in_channel = open_in file in
	try
	  while true do
		let line = input_line in_channel in
		(* do something with line *)
		let factor = Array.init (String.length line) (fun i -> (int_of_char line.[i]) - 48) in (*ASCII code for '0' is 48*)
		res := tree_add (!res) factor (Array.length factor - 1) false
	  done;
	  (!res)
	with End_of_file ->
	  close_in in_channel; (!res)
;;

let exists_file file =
	try
		let in_channel = open_in file in
		close_in in_channel;
		true
	with Sys_error s -> false
;;(* TODO Sys.file_exists already does this !*)

(*hardcoded function for file names already given in the form tree_files/f_reduc_steps_maxSize.txt*)
let exists_before reduc steps min max dir_name =
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

(*****************************************************************************)
(*                   Definition of Printer functions                         *)
(*****************************************************************************)

let print_rat (r:rat) = match r with
	| (p,q) -> Printf.printf "%d/%d\n" p q
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

let print_array_of_array a =
	print_string "[|\n";
	for i = 0 to Array.length a - 2 do
		print_array a.(i); print_string ";"
	done;
	if Array.length a > 0 then print_array a.(Array.length a -1);
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

let print_tree_as_factors t = 
	print_string "[|";
	let rec aux t str = match t with
		| Nil -> ()
		| Leaf -> print_list_as_word str (*doubly reversed*)
		| Node(t1,t2) -> aux t1 (0::str); print_string ";"; aux t2 (1::str)
	in aux t []
;;






let complement word =
	let res = Array.make (Array.length word) 0 in
	for i = 0 to (Array.length word - 1) do
		res.(i) <- 1-word.(i)
	done;
	res
;;



(*Debugging function : prints the cases of the table that were computed.*)
let print_empty a = 
	for i = 0 to Array.length(a)-1 do
		for j = 0 to Array.length(a.(0))-1 do
			if a.(i).(j) = Nil then print_string "o"
			else print_string "x";
		done;
		print_string "\n";
	done
;;

let find_factors_1_from_scratch to_forbid reduc max_size =
	let word = Array.make max_size (-1) in
	let rec find_factors_1 pos =
	for bit=0 to 1 do
		let new_pos = pos+1 in
		word.(new_pos) <- bit;
		if (new_pos >= 2*reduc-1) && not(still_has_no_big_square word new_pos reduc) then begin
		(*Forbidden iff it has a big square, no need to check if it was already forbidden or not.*)
		(*Here : word is forbidden*)
			if not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) then begin  (*no need to add factor if a smaller one is already in tree*)
				(*if Array.sub word 0 9 = [|0;0;0;1;0;1;1;0;1|] then
				begin
						print_list_of_list (tree_to_list_of_factors (!to_forbid));
						Printf.printf "Bad word added to tree.\n";
						Printf.printf "test of belonging : %b\n" (not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)));
						Printf.printf "test of coherence : %b\n" (not(is_suffix_in_mirrors_tree [|0;1;0;0;1;0|] 5 (!to_forbid)));
				end;*)
				let square = smallest_suffix_square_above_period word new_pos reduc in
				to_forbid := tree_add (!to_forbid) square (Array.length square -1) true;
				to_forbid := tree_add (!to_forbid) square (Array.length square -1) false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
				to_forbid := tree_add (!to_forbid) (complement square) (Array.length square -1) true; (*complement of word is also forbidden*)
				to_forbid := tree_add (!to_forbid) (complement square) (Array.length square -1) false;
			end
		end
		else if new_pos < (max_size - 1) then (*otherwise length is size max_size, no need to check next letters, limit is reached*)
			find_factors_1 new_pos; (* this word is okay, look for something forbidden later *)
		word.(new_pos) <- -1 (*going backward requires to clean end of word*)
	done;
	in find_factors_1 (-1)
;;



let wrong_factors max_step max_sizes alpha_inv = (*Generalise 1/3 to any alpha rational -> replace "3" with alpha^-1*)
	let alpha = rat_inv (alpha_inv) in
	(*let ceil_min_period = rat_ceil alpha in*)
	let floor_min_period = rat_floor alpha in
	let tot_letters = (rat_ceil (mult_by_int alpha max_step)) in (*number of letters to remove in total*)
	let forbidden = Array.make_matrix (tot_letters+1) (max_step+1) Nil in
	let dir_name = match alpha_inv with
		| (p,q) -> "tree_files_"^ (string_of_int p)^"_"^(string_of_int q)
	in
	(*forbidden(r,s) contains all factors in which we can retrieve r-3l letters within s-l reduction steps,
	for 0 <= l <= max(s-1, r/3) --> prog dyn.
	Those will be our forbidden factors : factors that we can reduce efficiently.
	Note : forbidden excludes big squares, this is a separate step of computation*)
	let rec build_forbidden reduc steps max_size =
		if forbidden.(reduc).(steps) != Nil then forbidden.(reduc).(steps) (*this has already been computed*)
		else let file_name_prefix = (dir_name^"/f_"^(string_of_int reduc)^"_"^(string_of_int steps)^"_") in
		let size_exist = (exists_before reduc steps max_size 50 dir_name) in
		if size_exist != 0 then begin
		(*TODO Warning ! ici je hardcode que je cherche si un fichier existe pour des tailles de facteur d'au plus 50, ça ne devrait pas dépasser.*)
			let forbid = get_tree_from_file (file_name_prefix^(string_of_int size_exist)^".txt") in
			(*Printf.printf "--> Factors of size at most %d from which we remove %d letters in %d steps were already computed (maybe in better max size)%!\n" max_size reduc steps;*)
			forbidden.(reduc).(steps) <- forbid;
			forbidden.(reduc).(steps)
		end
		else begin
			(* Base case : check that retrieving any square of size 1 or 2 does not make appear
			a big square in the word (of size 4 or 5) *)
			if steps = 1 then
			begin
				let to_forbid = ref Nil in
				(*Printf.printf "Début d'un cas de base\n%!";*)
				find_factors_1_from_scratch to_forbid reduc max_size;
				forbidden.(reduc).(steps) <- (!to_forbid);
				Printf.printf "--> Done computing factors of size at most %d from which we remove %d letters in %d steps%!\n" max_size reduc steps;
				(*Printf.printf "Adding corresponding tree to file %s!%!\n" (file_name_prefix^(string_of_int max_size)^".txt");*)
				write_tree_to_file forbidden.(reduc).(steps) (file_name_prefix^(string_of_int max_size)^".txt");
				let size_exist = (exists_before reduc steps 1 (max_size-1) dir_name) in (* this checks if a file existed with smaller factor size *)
				if size_exist != 0 then (* TODO Warning : same as above*)
				(*Delete previous file if factors were computed with a bigger size, only keep the better (bigger) tree *)
					Sys.remove (file_name_prefix^(string_of_int size_exist)^".txt");
				
				forbidden.(reduc).(steps)
			end
			
			(* Recursive call *)
			else (* expected that steps is at least 3 here, not steps = 1 *)
			begin
				(*Printf.printf "Début d'un appel récursif %!\n";*)
				if (reduc - floor_min_period <= 2) then Printf.printf "NOT Normal to remove less than 2 letters from floor, here reduc = %d and floor = %d-------------! and steps = %d%!\n" reduc floor_min_period steps;
				(*if (reduc - floor_min_period) < rat_ceil (mult_by_int alpha (steps-1)) then
					(Printf.printf "Absurd: we want to remove only %d letters within %d steps ! (floor)\n" (reduc - floor_min_period) (steps-1); raise BadValue);
				*)
				let to_forbid = ref (build_forbidden (reduc - floor_min_period) (steps-1) max_size) in
				(*Printf.printf "Adding factors forbidden from removing %d letters in %d steps\n" (reduc - floor_min_period) (steps-1);
				Printf.printf "Verdict1 : %b\n" (not(is_suffix_in_mirrors_tree [|0;1;0;0;1;0|] 5 (!to_forbid)));
				Printf.printf "Verdict2 : %b\n" (not(is_suffix_in_mirrors_tree [|1;1;1;0;1;0;0;1;0|] 8 (!to_forbid)));*)
				if (reduc+1 < Array.length forbidden) && forbidden.(reduc+1).(steps) != Nil then
					to_forbid := union (!to_forbid) forbidden.(reduc+1).(steps);
				(*Careful : floor here because we're not sure it is enough to remove "only" reduc-ceil letters, 
				this can make us miss some factors in rational case :/*)
				
				(*to speed up search of factors when we have the factors of smaller size already, start from its tree and don't look at word before its size*)
				let threshold = ref 0 in 
				let size_exist = (exists_before reduc steps 1 max_size dir_name) in
				if size_exist != 0 then begin
					let forbid_less = get_tree_from_file (file_name_prefix^(string_of_int size_exist)^".txt") in
					to_forbid := union (!to_forbid) forbid_less;
					threshold := size_exist;
					(*Printf.printf "We start from previously found prefixes of size %d\n" size_exist;*)
				end;
				
				(*if reduc = 7 && steps = 2 then
					print_list_of_list (tree_to_list_of_factors (!to_forbid));*)
				
				(*This way forbidden_factors will contain every factor nicely reducible in any number of steps except just 1 step : separately*)
				let word = Array.make max_size (-1) in
				let rec find_factors pos =
					for bit=0 to 1 do
						let new_pos = pos+1 in
						word.(new_pos) <- bit;
						(*if Array.sub word 0 9 = [|1;1;1;0;1;0;0;1;0|] then
						begin
								(*print_list_of_list (tree_to_list_of_factors (!to_forbid));*)
								Printf.printf "reached by step 2\n";
								Printf.printf "test of belonging : %b\n" (not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)));
								Printf.printf "test of coherence : %b\n" (not(is_suffix_in_mirrors_tree [|0;1;0;0;1;0|] 5 (!to_forbid)));
						end;*)
						if not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)) then (*don't bother look if word already has a factor in to_forbid*)
						begin
							(*if Array.sub word 0 9 = [|1;1;1;0;1;0;0;1;0|] then
								Printf.printf "absurde\n";*)
							(*if Array.sub word 0 8 = [|0;0;0;1;0;0;0;1|] && new_pos = 7 then
							begin
								(*print_list_of_list (tree_to_list_of_factors (!to_forbid));*)
								print_array word;
								Printf.printf "Looking at target BLA\n";
								Printf.printf "We want to remove %d letters from it in %d steps\n" reduc steps;
								Printf.printf "Verdict : %b\n" (not(is_suffix_in_mirrors_tree word new_pos (!to_forbid)));
								raise BadValue;
							end;*)
							if new_pos >= reduc-1 && new_pos >= (!threshold) && 
							(not(still_has_no_big_square word new_pos (reduc-1)) (*tested separately from is_forbidden for speedup*)
							|| is_forbidden word new_pos reduc steps max_size) then begin (*forbidden word by one step of reduc*)
								to_forbid := tree_add (!to_forbid) word new_pos true;
								to_forbid := tree_add (!to_forbid) word new_pos false; (*if a factor is forbidden, then by same reductions so is its mirror.*)
								to_forbid := tree_add (!to_forbid) (complement word) new_pos true; (*complement of word is also forbidden*)
								to_forbid := tree_add (!to_forbid) (complement word) new_pos false;
							end
							else if new_pos < (max_size - 1) then (*otherwise length is size max_size, no need to check next letters, limit is reached*)
								find_factors new_pos; (* this word is okay, look for something forbidden later *)
						end;
						word.(new_pos) <- -1 (*going backward requires to clean end of word*)
					done;
				in
				(*Printf.printf "Début du backtrack%!\n";*)
				find_factors (-1);
				forbidden.(reduc).(steps) <- (!to_forbid);
				Printf.printf "--> Done computing factors of size at most %d from which we remove %d letters in %d steps%!\n" max_size reduc steps;
				
				(*Printf.printf "Adding corresponding tree to file %s!%!\n" (file_name_prefix^(string_of_int max_size)^".txt");*)
				write_tree_to_file forbidden.(reduc).(steps) (file_name_prefix^(string_of_int max_size)^".txt");
				let size_exist = (exists_before reduc steps 1 (max_size-1) dir_name) in (* this checks if a file existed with smaller factor size *)
				if size_exist != 0 then (* TODO Warning : same as above*)
				(*Delete previous file if factors were computed with a bigger size, only keep the better (bigger) tree *)
					Sys.remove (file_name_prefix^(string_of_int size_exist)^".txt");
				
				
				forbidden.(reduc).(steps) (*returns asked result : a tree of forbidden factors, ie reducing r letters within s steps*)
			end
		end
	
	and is_forbidden word n reduc steps max_size =
		(** Checks that no reduction in "word" of a square of size 1 or 2 leads to a forbidden word,
		ie a word containing a factor from corresponding tree of suffix forbid_1 or 2 (corresponding to description below) *)
		let res = ref false in
		let pos = ref 0 in
		let max_period = reduc - 2 in
		while not(!res) && (!pos) < n do (*look for small squares beginning at pos, no use to check last letter*)
			let period = ref max_period in
			while not(!res) && (!period) >= 1 do
				let is_square = ref true in
				if (!pos + 2*(!period)-1) > n then is_square := false;
				let pos_square = ref 0 in
				while !is_square && pos_square < period do (* check we have a square of size period at pos "pos" *)
					if word.(!pos + (!pos_square)) != word.(!pos + (!period) + (!pos_square)) then
						is_square := false;
					pos_square := !pos_square + 1;
				done;
				if (!is_square) then begin
					let reduc_word = Array.append (Array.sub word 0 (!pos)) (Array.sub word (!pos+(!period)) (n-(!pos+(!period))+1)) in
					if (reduc - !period <= 2) then begin
						Printf.printf "NOT Normal to remove less than 2 letters, here reduc = %d and period = %d and steps = %d-------------!%!\n" (reduc) (!period) steps;
					Printf.printf "Word seen is :\n";
					print_array word;
					Printf.printf "After reduction seen is :\n";
					print_array reduc_word;
					raise BadValue
					end;
					(*if (reduc - (!period)) < rat_ceil (mult_by_int alpha (steps-1)) then begin
						(Printf.printf "Absurd: we want to remove only %d letters within %d steps ! (condition)\n" (reduc - (!period)) (steps-1));
						Printf.printf "Because we are looking at below word from which we want to remove %d letters in %d steps\n" reduc steps;
						print_array word;
						Printf.printf "After reduction is left :\n";
						print_array reduc_word;
						raise BadValue
					end;*)
					if (has_factor_in_tree reduc_word ((Array.length reduc_word) - 1) (build_forbidden (reduc - (!period)) (steps-1) max_size))(*period is the number of letter we removed*)
					then (*case forbidden in one step done separately*)
						res := true;
					if (reduc - !period <= 2) then Printf.printf "Word is forbidden : %b\n" (!res);
				end;
				period := !period - 1;
			done;
			pos := (!pos + 1)
		done;
		!res
	
	in 
	let res = ref Nil in
	let enough = ref false in
	let nb_steps = ref 1 in
	while not(!enough) && (!nb_steps) <= max_step do
		let tight_tree = build_forbidden (rat_ceil (mult_by_int alpha (!nb_steps))) (!nb_steps) (max_sizes.(!nb_steps)) in
		res := union (!res) tight_tree;
		Printf.printf "Added factors forbidden in %d steps of size at most %d\n%!" (!nb_steps) max_sizes.(!nb_steps);
		Printf.printf "We forbid %d factors in total\n" (nb_of_factors_in_tree (!res));
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


