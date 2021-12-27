
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

exception BadValue;; (* This exception means that something else than a bit 0 or 1 was read. *)
exception Empty;; (* This means a word (as a predefined array of -1) lacks a letter at an observed position. *)
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



(*****************************************************************************)
(*                     Binary tree type and functions                        *)
(*****************************************************************************)

(* This type will be used to store efficiently all factors of a given size in a word.
We don't need any label, all that matters is the shape of the tree.
Edges represent bits: 
	* Left child -> 0
	* Right child -> 1
A Leaf symbolizes the end of a valid word, and Nil represents the absence of child (or an empty tree).*)

type 'a tree =
	| Nil
    | Leaf
    | Node of 'a tree * 'a tree (*left = 0, right = 1*)
;;


let rec tree_add t w d =
	(** Adds prefix of size f from binary word w to binary tree t *)
	if d = 0 then match t with (* we read a complete word, eg "0110010", to get here *)
	(*After adding a word, we want to finish on a Leaf.*)
	| Nil -> Leaf 
	| t -> t (*this will only match a Leaf, since all factors added to the tree will have same size*)
	else match w with
	| [] -> t
	| 0 :: ww -> begin match t with
		| Nil -> Node(tree_add Leaf ww (d-1), Nil)
		| Leaf -> Node(tree_add Leaf ww (d-1), Nil)
		| Node(t1,t2) -> Node(tree_add t1 ww (d-1), t2)
		end
	| 1 :: ww -> begin match t with
		| Nil ->  Node(Nil, tree_add Leaf ww (d-1))
		| Leaf -> Node(Nil, tree_add Leaf ww (d-1)) (*not supposed to happen, all factors have same length *)
		| Node(t1,t2) -> Node(t1, tree_add t2 ww (d-1))
		end
	| _ -> raise BadValue
;;


let rec tree_add_arr t word pos d =
	(** Same as tree_add but the word is in a predefined array instead of a list.
	Suffix observed begins at index "pos" and has size d. *)
	(*Printf.printf "looking at pos %d of word\n" pos;*)
	if d = 0 then match t with
	| Nil -> Leaf (* on a lu un mot pour arriver là *)
	| t -> t
	else match word.(pos) with
	| 0 -> begin match t with
		| Nil -> Node(tree_add_arr Leaf word (pos+1) (d-1), Nil)
		| Leaf -> Node(tree_add_arr Leaf word (pos+1) (d-1), Nil)
		| Node(t1,t2) -> Node(tree_add_arr t1 word (pos+1) (d-1), t2)
		end
	| 1 -> begin match t with
		| Nil ->  Node(Nil, tree_add_arr Leaf word (pos+1) (d-1))
		| Leaf -> Node(Nil, tree_add_arr Leaf word (pos+1) (d-1)) (*not supposed to happen, all factors have same length *)
		| Node(t1,t2) -> Node(t1, tree_add_arr t2 word (pos+1) (d-1))
		end
	| -1 -> raise Empty
	| _ -> raise BadValue
;;


let rec is_in_tree word factors = (*just check that  *)
	(** Checks that the mirror of the d-sized suffix from "word" (as a list) is not in the "factors" tree,
	where d is the size of the factors contained in tree. *)
	match word, factors with
	| [], Leaf -> true (*we just read the word and ended on a leaf !*)
	| _, Nil -> false (* Can't be in empty tree, we must have taken a branch leading to non-existing path Nil *)
	| h::t, Leaf -> raise NonMatchingSize (* not supposed to happen : tree and word are same length/depth *)
	| 0::t, Node(t1,t2) -> is_in_tree t t1
	| 1::t, Node(t1,t2) -> is_in_tree t t2
	| _, _ -> raise BadValue
;;
(*Above function is used to check that a word is still d-directed after adding one last letter.
Tree of factors must contain all d-sized factors from word, including d-sized suffix.*)


let rec is_mirror_in_tree word pos factors d = 
	(** Same as "is_in_tree" but the word is in a predefined array.
	Checks that the mirror of the factor of length d beginning at index pos is in the tree *)
	match factors with
	| Leaf -> if d = 0 then true else raise NonMatchingSize (* not supposed to happen : tree and word are same length/depth *)
	| Nil -> false
	| Node(t1,t2) -> match word.(pos+d-1) with
		| 0 -> is_mirror_in_tree word pos t1 (d-1)
		| 1 -> is_mirror_in_tree word pos t2 (d-1)
		| -1 -> raise Empty
		| _ ->  raise BadValue
;;
(*Above function is used only in general test is_d_directed_and_alpha_free below.*)




(*****************************************************************************)
(*                     Directedness and freeness tests                       *)
(*****************************************************************************)

(* ---------- d-directedness ---------- *)

let is_not_d_directed_anymore word factors d =
	(** Checks that "word" is not d-directed anymore after adding the last letter,
	i.e. the letter at the head of the list. *)
	is_in_tree (List.rev (isolate_factor word d)) factors
	(*Careful, the word represented as a list is reversed.*)
;;

let is_d_directed w d = 
	(** General test checking if word "w" is d-directed. *)
	let rec aux_is_d w factors = match w with
	| [] -> true (*when deleting this useless line, ocaml outputs a warning*)
	| w0 when List.length w0 < d -> true
	| h::t -> let new_factors = tree_add factors w d in
		not(is_not_d_directed_anymore w new_factors d) && aux_is_d t new_factors
	in
	aux_is_d w Nil
;;


(* ---------- Alpha-freeness ---------- *)

let is_still_alpha_free word n alpha plus =
	(** Checks that "word" is still alpha-free after adding the last letter,
	which is at index n in the array representing the word. *)
	let max_alpha = ref ((1,1):rat) in
	let res = ref true in
	let p = ref 1 in
	while !res && (!p) <= int_of_float ((float_of_int (n+1))/. (float_of_rat alpha)) + 1 do (*p is the tested period, +1 is to be sure*)
		let pos = ref (n-(!p)) in
		let end_of_repetition = ref false in
		while not(!end_of_repetition) && !pos >= 0 do
			if word.(!pos) != word.(!pos+(!p)) then
				end_of_repetition := true
			else
				pos := !pos - 1				
		done;
		max_alpha := max_rat !max_alpha (n-(!pos), (!p));
		if plus && (gt !max_alpha alpha) then res := false (*we must not have repetition of size more than alpha, except alpha itself *)
		else if (not plus) && ge !max_alpha alpha then res := false; (*we must not have repetition of size alpha (or more) *)
		p := !p + 1
	done;
	!res
;;

let is_alpha_free word alpha plus =
	(** General test checking if "word" is alpha-free. *)
	let res = ref true in
	let i = ref 0 in
	while !res && !i < Array.length word do
		if not(is_still_alpha_free word (!i) alpha plus) then
			res := false;
		i := !i + 1
	done;
	!res
;;


(* ---------- General test ---------- *)

let is_d_directed_and_alpha_free word d alpha plus =
	(** General test checking if "word" is alpha-free and d-directed. *)
	let res = ref true in
	let factors = ref Nil in
	let i = ref 0 in
	while !res && !i < Array.length word do
		if !i >= d-1 then
		begin
			factors := tree_add_arr (!factors) word (!i-d+1) d;
			if is_mirror_in_tree word (!i-d+1) (!factors) d then
				res := false;
		end;
		if not(is_still_alpha_free word (!i) alpha plus) then
			res := false;
		i := !i + 1
	done;
	!res
;;



(*****************************************************************************)
(*                Morphism conditions tests on three words                   *)
(*****************************************************************************)


let stays_alpha_free l1 l2 l3 alpha plus =
	(** Checks that any concatenation without squares
	of three words l1, l2 and l3 stay alpha-free. *)
	is_alpha_free (Array.of_list (l1@l2@l1)) alpha plus &&
	is_alpha_free (Array.of_list (l1@l3@l1)) alpha plus &&
	is_alpha_free (Array.of_list (l1@l3@l2)) alpha plus &&
	is_alpha_free (Array.of_list (l2@l1@l2)) alpha plus &&
	is_alpha_free (Array.of_list (l2@l1@l3)) alpha plus &&
	is_alpha_free (Array.of_list (l2@l3@l1)) alpha plus &&
	is_alpha_free (Array.of_list (l2@l3@l2)) alpha plus &&
	is_alpha_free (Array.of_list (l3@l1@l2)) alpha plus &&
	is_alpha_free (Array.of_list (l3@l1@l3)) alpha plus &&
	is_alpha_free (Array.of_list (l3@l2@l1)) alpha plus &&
	is_alpha_free (Array.of_list (l3@l2@l3)) alpha plus
;;

exception Is_false;; (* Used to interrupt below function when a required condition is already proved false. *)

let is_synchronized w1 w2 w3 l =
	(** Checks that three words w1 w2 and w3 satisfy the synchronizing condition from Lemma 2.1.
	(i.e. no word is a strict factor of the concatenation of two others). *)
	let w11 = Array.append w1 w1 in
	let w12 = Array.append w1 w2 in
	let w13 = Array.append w1 w3 in
	let w21 = Array.append w2 w1 in
	let w22 = Array.append w2 w2 in
	let w23 = Array.append w2 w3 in
	let w31 = Array.append w3 w1 in
	let w32 = Array.append w3 w2 in
	let w33 = Array.append w3 w3 in
	try
	for i = 1 to l-1 do (* strict factor, can be equal*)
		if Array.sub w11 i l = w1 || Array.sub w11 i l = w2 || Array.sub w11 i l = w2 then raise(Is_false)
		else if Array.sub w12 i l = w1 || Array.sub w12 i l = w2 || Array.sub w12 i l = w3 then raise(Is_false)
		else if Array.sub w13 i l = w1 || Array.sub w13 i l = w2 || Array.sub w13 i l = w3 then raise(Is_false)
		else if Array.sub w21 i l = w1 || Array.sub w21 i l = w2 || Array.sub w21 i l = w3 then raise(Is_false)
		else if Array.sub w22 i l = w1 || Array.sub w22 i l = w2 || Array.sub w22 i l = w3 then raise(Is_false)
		else if Array.sub w23 i l = w1 || Array.sub w23 i l = w2 || Array.sub w23 i l = w3 then raise(Is_false)
		else if Array.sub w31 i l = w1 || Array.sub w31 i l = w2 || Array.sub w31 i l = w3 then raise(Is_false)
		else if Array.sub w32 i l = w1 || Array.sub w32 i l = w2 || Array.sub w32 i l = w3 then raise(Is_false)
		else if Array.sub w33 i l = w1 || Array.sub w33 i l = w2 || Array.sub w33 i l = w3 then raise(Is_false)
	done;
	true
	with Is_false -> false
;;



(*****************************************************************************)
(*                              Backtrackings                                *)
(*****************************************************************************)


exception Sortir of (int list);; (* This exception is used to interrupt a backtracking when
the result is found, instead of finishing going through every possible word.
Result must be passed as a word. *)

exception Sortir0;; (* Same but the word is in a global variable array, so no need to pass arguments. *)

exception Sortir2 of (int list list);; (* Same but the words will be given as a list of 3 words,
that will be the images of the letters of a ternary alphabet by a homomorphism.*)


let d_directed d l =
	(** A first very simple backtracking that generates a d-directed word of size l.
	Returns [] if none exists.*)
	let rec d_directed_aux word factors =
		if List.length(word) = l then raise (Sortir word)
		else begin
			for bit=0 to 1 do
				if List.length(word) >= (d-1) then begin (*bit we add will form a new factor !*)
					let new_factors = tree_add factors (bit :: word) d in
					if not(is_not_d_directed_anymore (bit :: word) new_factors d) then
						d_directed_aux (bit :: word) new_factors
				end
				else d_directed_aux (bit :: word) factors
			done;
		end
	in try d_directed_aux [] Nil;
	[]
	with Sortir(word) -> List.rev word
;;


let d_directed_alpha_free d alpha l plus = (*l is maximal length of word we want*)
	(** Backtracking generating a alpha-free (or alpha+-free if plus is set to true)
	and d-directed word of size l. Returns [||] if none exists. *)
	let word = Array.make l (-1) in
	let rec aux factors pos =
		for bit=0 to 1 do
			let pos = pos+1 in
			word.(pos) <- bit;
			if pos >= d-1 then (*bit we add will form a new factor*)
			begin 
				let factors = tree_add_arr factors word (pos-d+1) d in
				if not(is_mirror_in_tree word (pos-d+1) factors d) && is_still_alpha_free word pos alpha plus then
				begin
					if pos = (l-1) then raise Sortir0 (*then length is l*)
					else aux factors pos
				end
			end
			else begin
				if is_still_alpha_free word pos alpha plus then
					aux factors pos;
				(*Else no need to continue backtracking*)
			end;
			word.(pos) <- -1 (*going backward requires to clean end of word*)
		done;
	in try aux Nil (-1);
	[| |]
	with Sortir0 -> word
;;


let homomorphism_alpha d l alpha plus = (* Need l >= d *)
	(** Generates by backtracking 3 words that are d-directed and alpha-free 
	such that any concatenation of them remains d-directed and alpha-free 
	and satisfies synchronizing*)
	let rec hom_aux current_word prefixes fst_suffix words factors=
		for bit=0 to 1 do
			let new_current_word = bit::current_word in
			if is_still_alpha_free (Array.of_list (List.rev new_current_word)) (List.length new_current_word - 1) alpha plus then
			begin (*else nothing to do : stop backtracking here, useless to continue with alpha-freeness broken*)
			
				let new_factors = tree_add factors new_current_word d in (*first d-bit is necessary to check in every case*)
				if List.length(current_word) < (d-1) then (*under that, no factor of size d -> nothing to check*)
					hom_aux (bit :: current_word) prefixes fst_suffix words factors
				else if not(is_in_tree (List.rev (isolate_factor new_current_word d)) new_factors) then (*else stop backtracking here*)
				begin
					let words = ref words in
					let fst_suffix = ref fst_suffix in 
					let prefixes = ref prefixes in	
					
					(****************************************************************************************)
					(* Modifying the remembered suffixes and prefixes if one of them is finished to be built*)
					if d = List.length(new_current_word)  || l+d = List.length(new_current_word) then begin
						prefixes := (List.rev (isolate_factor new_current_word d))::!prefixes
					end;
					(*memorize the suffix of the "first" word of size l finished*)
					if l = List.length(new_current_word) then begin
						fst_suffix := (isolate_factor new_current_word d);
						words := (isolate_factor new_current_word l) :: !words
					end;
					
					(*****************************************************************************)
					(*End of second word : must check all concat with prefix from first word*)
					if 2*l = List.length(new_current_word) then 
					begin
						words := (isolate_factor new_current_word l)::!words;
						let still_true = ref true in
						let i = ref 1 in
						let new_factors = ref new_factors in
						while !still_true && !i < d do
							let partial_factor = (List.rev (isolate_factor new_current_word !i)) in (*this is end of suffix*)
							let complementary_prefix = (isolate_factor (List.hd(List.tl (!prefixes))) (d-(!i))) in (*this is beginning of prefix*)
							(*prefixes contains prefix of first and second word, we access first word that was added first*)
							let factor = List.rev (partial_factor @ complementary_prefix) in (*as always, factor is given in opposite direction*)
							new_factors := tree_add !new_factors factor d;
							if is_in_tree (List.rev factor) !new_factors then
								still_true := false;
							i := !i+1;
						done;
						if !still_true then
						begin
							begin match !words with
								| [l2;l1] -> still_true := is_alpha_free (Array.of_list ((List.rev l2)@(List.rev l1))) alpha plus;
								| _ -> raise NonMatchingSize (*not supposed to happen*);
							end;
							if !still_true then
								hom_aux new_current_word !prefixes !fst_suffix !words !new_factors
						end;
						(*else stop backtracking here*)
					end
					
					(****************************************************************************************************************)
					(*Beginning of third and last word : in this case add a check for every factor made from the end of first suffix*)
					else if (2*l+1 <= List.length(new_current_word) && List.length(new_current_word) <= 2*l+d-1) then
					begin
						let partial_length = (List.length(new_current_word) mod l) in
						let partial_factor = (isolate_factor new_current_word partial_length) in
						let complementary_suffix = (isolate_factor (!fst_suffix) (d - partial_length)) in
						let mix_up_factor = partial_factor@complementary_suffix in
						let new_factors = tree_add new_factors mix_up_factor d in
						if not(is_in_tree (List.rev mix_up_factor) new_factors) then
							hom_aux new_current_word !prefixes !fst_suffix !words new_factors
					end
											
					(***********************************************************************************)
					(*End of last word : must check all concat with prefixes from first and second word*)
					else if 3*l = List.length(new_current_word) then 
					begin
						words := (isolate_factor new_current_word l)::!words;
						let still_true = ref true in
						let new_factors = ref new_factors in
						
						(*checking that adding a beginning of prefix from first 2 words preserves d-directedness*)
						for prefix=0 to 1 do
							let i = ref 1 in
							while !still_true && !i < d do
								let partial_factor = List.rev (isolate_factor new_current_word !i) in
								let complementary_prefix = (if prefix = 0 then ((isolate_factor (List.hd(List.tl !prefixes)) (d-(!i))))
									else ((isolate_factor (List.hd(!prefixes)) (d-(!i))))) in 
								(*prefixes contains prefix of first and second word, we access first word that was added first*)
								let factor = List.rev (partial_factor @ complementary_prefix)  in (*as always, factor is given in opposite direction*)
								new_factors := tree_add !new_factors factor d;
								if is_in_tree (List.rev factor) !new_factors then
									still_true := false;
								i := !i+1
							done;
						done;
						
						(* Now we have three d-directed words in any concatenation,
						still need to check alpha-freeness is also preserved by permutations *)
						if !still_true then begin
							match !words with
							| [l3;l2;l1] -> let ll1 = List.rev l1 in
								let ll2 = List.rev l2 in
								let ll3 = List.rev l3 in
								if not(ll1 = ll2) && not(ll1 = ll3) && not(ll2 = ll3) && 
								stays_alpha_free ll1 ll2 ll3 alpha plus then raise (Sortir2 !words)
							| _ -> raise NonMatchingSize (*not supposed to happen*)
						end
					end
					(*otherwise : not end of a word*)
													
					(********************************)
					(*None of the "hard" cases above*)
					else
						hom_aux new_current_word !prefixes !fst_suffix !words new_factors
				end
			end
		done;
	in try hom_aux [] [] [] [] Nil;
	[]
	with Sortir2(words) -> List.map List.rev words
;;



(*****************************************************************************)
(*                          Dichotomy on alpha                               *)
(*****************************************************************************)


exception DichotomyOutOfRange;;

let dichotomy (mini : rat) (maxi : rat) d l =
	(** Searches by dichotomy for the alpha that is tight for d.
	ie there exists a d-directed alpha+-free word (of size l large) but no d-directed alpha-free word (of size at least l) *)
	let alpha_min = ref mini in
	let alpha_max = ref maxi in
	let alpha_inter = ref mini in
	let found = ref false in
	
	(*Testing alpha_max :*)
	let w = (d_directed_alpha_free d (!alpha_max) l false) in
	let w_plus = (d_directed_alpha_free d (!alpha_max) l true) in
	if w = [||] && w_plus != [||] then
		begin found := true; alpha_inter := (!alpha_max) end;
	if w_plus = [||] then
		raise DichotomyOutOfRange; (*Even our maximum alpha is too much a constraint, can't find alpha tight.*)
	
	(*Testing alpha_min :*)
	let w = (d_directed_alpha_free d (!alpha_min) l false) in
	let w_plus = (d_directed_alpha_free d (!alpha_min) l true) in
	if w = [||] && w_plus != [||] then
		found := true;
	if w != [||] then
		raise DichotomyOutOfRange; (*Even our minimum alpha is not enough of a constraint, can't find alpha tight.*)
	
	(*Now that we know alpha is indeed between alpha_min and alpha_max, go on with the dichotomy :*)
	while not(!found) && ge (rat_minus (!alpha_max) (!alpha_min)) (1,100) (* top when difference is <= 1/100 *)
	do
		alpha_inter := inter (!alpha_min) (!alpha_max);
		let w = (d_directed_alpha_free d (!alpha_inter) l false) in
		let w_plus = (d_directed_alpha_free d (!alpha_inter) l true) in
		if w = [||] && w_plus != [||] then
			found := true
		else begin
			if w_plus = [||] then alpha_min := (!alpha_inter) (*in this case alpha is too strong a constraint,
			we can't find a word that is even alpha_inter+-free. Need to allow a bigger alpha, thus increase alpha_min.*)
			else alpha_max := (!alpha_inter) (*in this case alpha is not enough of a constraint, 
			we can even find a alpha_inter-free word (without plus). Need to reduce alpha.*)
		end
	done;
	!alpha_inter
;;

	
