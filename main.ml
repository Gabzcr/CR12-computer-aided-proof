
type 'a tree =
	| Nil
    | Leaf
    | Node of 'a tree * 'a tree;; (* no need of labels, left = 0, right = 1*)

let rec print_tree t = match t with
	| Nil -> Printf.printf ""
	| Leaf -> Printf.printf "."
	| Node(t1,t2) -> Printf.printf "Node("; print_tree t1; Printf.printf ","; print_tree t2; Printf.printf ")"
;;

let print_list l =
	let rec print_elements = function
		| [] -> ()
		| h::t -> print_int h; print_string ";"; print_elements t
	in
	print_string "[";
	print_elements l;
	print_string "]\n"
;;

let print_list_of_list l =
	let rec print_elements = function
		| [] -> ()
		| h::t -> print_int h; print_string ";"; print_elements t
	in
	print_string "[";
	let rec print_aux l = match l with
		| [] -> ()
		| w1::ww -> print_string "["; print_elements w1; print_string "]; "; print_aux ww
	in print_aux l;
	print_string "]\n"
;;


(* Test :
print_tree(Node(Leaf,Nil));;
Printf.printf "\n";;
*)

exception BadValue;;
exception BadValue2;;
exception BadValue3;;
let rec tree_add t w d =
	if d = 0 then match t with
	| Nil -> Leaf (* on a lu un mot pour arriver là *)
	| t -> t (* actually, can only be a leaf here *)
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

(* Test :
let t = tree_add Nil [0;1;1;0;0] 5;;
print_tree(t);;
Printf.printf "\n";;
let  t2 = tree_add t [0;1;1;1;0] 6;;
print_tree(t2);;
Printf.printf "\n";;
*)


let rec is_prefix word factor = match factor, word with (*Finally unused function*)
	| [],_ -> true
	| _,[] -> false
	| fa::fl, wa::wl -> (fa = wa) && is_prefix wl fl
;;

(* Test :
Printf.printf "%b\n" (is_prefix [0;1;1;0;0;0] [0;1;1]);;
Printf.printf "%b\n" (is_prefix [0;1;1;0;0;0] [0;1;0]);;
*)

exception TooShortList
let rec isolate_factor word d =
	if d = 0 then [] else match word with
	| [] -> raise TooShortList
	| h :: t -> h :: (isolate_factor t (d-1))
;;

(*Test :
print_list (isolate_factor [0;1;1;0;0;1] 3);;
Printf.printf "\n";;
*)

exception NonMatchingSize
let rec is_in_tree word factors = (*just check that the mirror of the last d-factor is not in the tree of factors *)
	match word, factors with
	| [], Leaf -> true (*we just read the word and ended on a leaf !*)
	| _, Nil -> false (* Can't be in empty tree, we must have taken a branch leading to non-existing path Nil *)
	| h::t, Leaf -> raise NonMatchingSize (* not supposed to happen : tree and word are same length/depth *)
	| 0::t, Node(t1,t2) -> is_in_tree t t1
	| 1::t, Node(t1,t2) -> is_in_tree t t2
	| _, _ -> raise BadValue2
;;

(* Test :
Printf.printf "is_in_tree1 :%b\n" (is_in_tree [0;1;1;0;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*true*)
Printf.printf "is_in_tree1 :%b\n" (is_in_tree [0;1;1;1;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*true*)
Printf.printf "is_in_tree1 :%b\n" (is_in_tree [0;1;0;1;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*false*)
*)

let is_not_d_directed_anymore word factors d =
	is_in_tree (List.rev (isolate_factor word d)) factors
;;

exception Sortir of (int list);;
let d_directed d l =
	let rec d_directed_aux word factors =
		if List.length(word) = l then raise (Sortir word)
		else begin
			for bit=0 to 1 do
				if List.length(word) >= (d-1) then begin (*bit we add will form a new factor !*)
					let new_factors = tree_add factors (bit :: word) d in
					(*Printf.printf "\nis_not_directed_anymore for :\n";
					print_list (bit :: word);
					Printf.printf "on tree of factors :\n";
					print_tree new_factors;
					Printf.printf "\nis %b:\n" (is_not_d_directed_anymore (bit :: word) new_factors d);*)
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

let d_directed_3_free d l =
	let rec d_directed_aux word factors current_chain =	
		if List.length(word) = l then raise (Sortir word)
		else begin
			for bit=0 to 1 do
				if List.length(word) >= (d-1) then begin (*bit we add will form a new factor !*)
					let new_factors = tree_add factors (bit :: word) d in
					(*Printf.printf "\nis_not_directed_anymore for :\n";
					print_list (bit :: word);
					Printf.printf "on tree of factors :\n";
					print_tree new_factors;
					Printf.printf "\nis %b:\n" (is_not_d_directed_anymore (bit :: word) new_factors d);*)
					if not(is_not_d_directed_anymore (bit :: word) new_factors d) then
					begin
						let current_chain = ref current_chain in
						if !current_chain = [] then 
						begin
							d_directed_aux (bit :: word) new_factors (bit :: !current_chain)
						end
						else if List.hd !current_chain = bit then 
						begin
							if List.length (!current_chain) = 1 then
								d_directed_aux (bit :: word) new_factors (bit :: !current_chain)
							(*else stop backtracking here*)
						end
						else (*List.hd != bit*)
							d_directed_aux (bit :: word) new_factors [bit]
					end
				end
				else begin
					let current_chain = ref current_chain in
						if !current_chain = [] then 
						begin
							d_directed_aux (bit :: word) factors (bit :: !current_chain)
						end
						else if List.hd !current_chain = bit then 
						begin
							if List.length (!current_chain) = 1 then
								d_directed_aux (bit :: word) factors (bit :: !current_chain)
							(*else stop backtracking here*)
						end
						else (*List.hd != bit*)
							d_directed_aux (bit :: word) factors [bit]
				end 
			done;
		end
	in try d_directed_aux [] Nil [];
	[]
	with Sortir(word) -> List.rev word
;;

(*
let d = 5	 in
let n = 1000 in
Printf.printf "%d-directed word of size %d :\n" d n;
print_list (d_directed_3_free d n);;
*)


let is_d_directed w d = 
	let rec aux_is_d w factors = match w with
	| [] -> true (*when deleting this useless line, ocaml outputs a warning*)
	| w0 when List.length w0 < d -> true
	| h::t -> let new_factors = tree_add factors w d in
		not(is_not_d_directed_anymore w new_factors d) && aux_is_d t new_factors
	in
	aux_is_d w Nil
;;

(* Test
Printf.printf "is_d_directed :%b\n" (is_d_directed [0;1;1;0;0] 3);; (*false*)
Printf.printf "is_d_directed :%b\n" (is_d_directed [1;0;1] 3);; (*false*)
Printf.printf "is_d_directed :%b\n" (is_d_directed [1;0;0] 3);; (*true*)
Printf.printf "is_d_directed :%b\n" (is_d_directed (d_directed 6 100) 6);; (*true*)
*)

(*
exception TooShortList
let rec isolate_factor_and_rest word d =
	if d = 0 then ([], word) else match word with
	| [] -> raise TooShortList
	| h :: t -> h :: (fst (isolate_factor_and_rest t (d-1))), snd (isolate_factor_and_rest t (d-1))
;;*)

(*Test :
print_list (fst (isolate_factor_and_rest [0;1;1;0;0;1] 3));;
print_list (snd (isolate_factor_and_rest [0;1;1;0;0;1] 3));;
Printf.printf "\n";;*)

(*
let cut_3l_in_3_l w l = 
	let w1, w_inter = isolate_factor_and_rest w l in
	let w2, w3 = isolate_factor_and_rest w_inter l in
	[w1; w2; w3]
;;*)

(* Test :
print_list_of_list (cut_3l_in_3_l [0;1;2;3;4;5;6;7;8] 3);; 
*)

(*Now work in one big array.
A subarray of this array is represented by a couple of indices (beginning, end)*)

(*
exception Is_false;;
let is_factor_at_pos (b1,e1) (b2,e2) arr p = (*checks if (b1,e1) is factor of (b2,e2) beginning at position p in (b2,e2)*)
	let n1 = e1-b1+1 in
	if n1 > e2-b2+1 then false 
	else try
	for i=0 to (n1-1) do
		if arr.(b1+i) != arr.(b2+p+i) then raise(Is_false)
	done;
	true
	with Is_false -> false
;;

Printf.printf "is_factor_at_pos :%b\n" (is_factor_at_pos (0,1) (2,6) [|1;0;0;1;1;0;0|] 1);; (*false*)
Printf.printf "is_factor_at_pos :%b\n" (is_factor_at_pos (0,1) (2,6) [|1;0;0;1;1;0;0|] 2);; (*true*)

let is_synchronized w l =
	let arr = Array.of_list w in
	let w1 = (0,l-1) in
	let w2 = (l, 2*l-1) in
	let w3 = (2*l, 3*l-1) in
	(*first check that w1 is not a factor of w2.w3*)
	for i = 0 to l do
		if is_factor_at_pos w1 (l, 3*l-1) arr i then raise(Is_false)
		else if is_factor_at_pos w3 (0, 2*l-1) arr i then raise(Is_false)
*)

exception Is_false;;
let is_synchronized w1 w2 w3 l =
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
	for i = 1 to l-1 do (* facteur strict, peut être égal*)
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

(* Test
Printf.printf "is_synchronized :%b\n" (is_synchronized [| 1;2;3 |] [| 4;5;1 |] [|2;3;6 |] 3);; (*false*)
Printf.printf "is_synchronized :%b\n" (is_synchronized [| 1;2;3 |] [| 4;5;6 |] [|2;3;6 |] 3);; (*true*)
*)

(*let is_any_concat_d_directed w1 w2 w3 d=
	is_d_directed (w2@w1) d && is_d_directed (w1@w3) d && is_d_directed (w2@w3)
;;*)


exception Sortir2 of (int list list);;
(* l >= d*)
let homomorphism d l = (*Generate by backtracking 3 words d-directed such that any concatenation of them remains d-directed
and satisfies synchronizing, i.e none of them is factor of concatenation of the two others.
--> word of size 3*l satisfying everything*)
	let rec hom_aux current_word prefixes fst_suffix words factors =
		for bit=0 to 1 do
			if List.length(current_word) >= (d-1) then (*under that, no factor of size d -> nothing to check*)
			begin
				let new_current_word = bit::current_word in
				let new_factors = tree_add factors new_current_word d in (*first d-bit is necessary to check in every case*)
				if not(is_in_tree (List.rev (isolate_factor new_current_word d)) new_factors) then (*else stop backtracking here*)
				begin
					let words = ref words in
					let fst_suffix = ref fst_suffix in 
					let prefixes = ref prefixes in	
					if d = List.length(new_current_word)  || l+d = List.length(new_current_word) then begin
						prefixes := (List.rev (isolate_factor new_current_word d))::!prefixes
					end;
					(*memorize the suffix of the "first" word of size l finished*)
					if l = List.length(new_current_word) then begin
						fst_suffix := (isolate_factor new_current_word d);
						words := (isolate_factor new_current_word l) :: !words
					end;
					
					(*case end of second word : must check all concat with prefix from first word*)
					if 2*l = List.length(new_current_word) then begin
						words := (isolate_factor new_current_word l)::!words;
						let still_true = ref true in
						let i = ref 1 in
						let new_factors = ref new_factors in
						while !still_true && !i < d do
							let partial_factor = (isolate_factor new_current_word !i) in
							let complementary_prefix = List.rev (isolate_factor (List.hd(List.tl (!prefixes))) (d-(!i))) in 
							(*prefixes contains prefix of first and second word, we access first word that was added first*)
							let factor = List.rev (complementary_prefix @ partial_factor) in (*as always, factor is given in opposite direction*)
							new_factors := tree_add !new_factors factor d;
							if is_in_tree (List.rev factor) !new_factors then
							begin
								still_true := false;
								(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
								Printf.printf "tested factor was :\n";
								print_list (factor);
								Printf.printf "backtrack was tried on :\n";
								print_list (new_current_word);	*)
							end;
							i := !i+1;
						done;
						if !still_true then hom_aux new_current_word !prefixes !fst_suffix !words !new_factors
						(*else stop backtracking here*)
					end
					else begin
						(*case end of third and last word : must check all concat with prefixes from first and second word*)
						if 3*l = List.length(new_current_word) then begin
							words := (isolate_factor new_current_word l)::!words;
							(*Printf.printf "Word of size 3*l reached ! : \n";
							print_list (current_word);
							Printf.printf "words contain :\n";
							print_list_of_list (!words);*)
							let still_true = ref true in
							let new_factors = ref new_factors in
							for prefix=0 to 1 do
								let i = ref 1 in
								while !still_true && !i < d do
									let partial_factor = (isolate_factor new_current_word !i) in
									let complementary_prefix = (if prefix = 0 then (List.rev (isolate_factor (List.hd(List.tl !prefixes)) (d-(!i))))
										else (List.rev (isolate_factor (List.hd(!prefixes)) (d-(!i))))) in 
									(*prefixes contains prefix of first and second word, we access first word that was added first*)
									let factor = complementary_prefix @ partial_factor in (*as always, factor is given in opposite direction*)
									new_factors := tree_add !new_factors factor d;
									if is_in_tree (List.rev factor) !new_factors then
									begin
										still_true := false;
										(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
										Printf.printf "tested factor was :\n";
										print_list (factor);
										Printf.printf "backtrack was tried on words:\n";
										print_list_of_list (!words);*)
									end;
									i := !i+1
								done;
							done;
							if !still_true then begin
								match !words with
								| [l1;l2;l3] -> let w1 = Array.of_list l1 in
									let w2 = Array.of_list l2 in
									let w3 = Array.of_list l3 in
									if is_synchronized w1 w2 w3 l then raise (Sortir2 !words)
									(*else begin
										Printf.printf "Word of size 3*l reached but not synchronized : \n";
										print_list (current_word);
										Printf.printf "words contain :\n";
										print_list_of_list (!words);
									end*)
								| _ -> raise BadValue3 (*not supposed to happen*)
							end
						end
						(*otherwise : not end of a word*)
						else
						begin
							(*case beginning of last word : in this case add a check for every factor made from the end of first suffix*)
							if (2*l+1 <= List.length(new_current_word) && List.length(new_current_word) <= 2*l+d-1) then
							begin
								let partial_length = (List.length(new_current_word) mod l) in
								let partial_factor = (isolate_factor new_current_word partial_length) in
								let complementary_suffix = (isolate_factor (!fst_suffix) (d - partial_length)) in
								let mix_up_factor = partial_factor@complementary_suffix in
								let new_factors = tree_add new_factors mix_up_factor d in
								if not(is_in_tree (List.rev mix_up_factor) new_factors) then
									hom_aux new_current_word !prefixes !fst_suffix !words new_factors
							end
							else
							(*None of the "mean" cases above*)
								hom_aux new_current_word !prefixes !fst_suffix !words new_factors
						end
					end
											
					
					(*if not(is_not_d_directed_anymore (bit :: word) new_factors d) then*)
						(*hom_aux (bit :: word) words new_factors*)
				end
			end
			else hom_aux (bit :: current_word) prefixes fst_suffix words factors
		done;
	in try hom_aux [] [] [] [] Nil;
	[]
	with Sortir2(words) -> List.map List.rev words
;;

(*Test
let d = 6 in
let l = 23 in
Printf.printf "%d-directed homomorphism of size %d :\n" d l;
print_list_of_list (homomorphism d l);;
*)

(*
let dmax = 15 in
for d = 5 to dmax do (*under 5 : no infinite d-directed word, so search would be infinite*)
	let l = ref d in
	let found = ref false in
	while not(!found) do
		let res = homomorphism d (!l) in
		if res != [] then begin
			Printf.printf "%d-directed words of size %d for homomorphism :\n" d (!l);
			print_list_of_list res;
			found := true
		end
		else l := !l + 1;
		if !l >= 30 then begin
			Printf.printf "No good triple of words of length <=30 were found for %d-directed words :\n" d;
			found := true
		end;
		flush stdout
	done;
done;
*)



type rat = int*int;; (*rational numbers*)

let gt (a:rat) (b:rat) =
	match a,b with
	|(p,q), (p',q') -> (p*q') > (p'*q)
;;

let ge (a:rat) (b:rat) = match a,b with
	|(p,q), (p',q') -> (p*q') >= (p'*q)
;;

let float_of_rat (r:rat) = match r with
	|(p,q) -> (float_of_int p)/.(float_of_int q)
;;

let max_rat (r1:rat) (r2:rat) = if ge r1 r2 then r1 else r2
;;

let print_rat (r:rat) = match r with
	| (p,q) -> Printf.printf "%d/%d\n" p q
;;

(*Test*)
Printf.printf "%b %b %b\n"

let print_array a =
	print_string "[|";
	for i = 0 to Array.length a - 2 do
		print_int a.(i); print_string ";"
	done;
	if Array.length a > 0 then print_int a.(Array.length a -1);
	print_string "|]\n"
;;


exception Empty;;
let rec tree_add_arr t word pos d =
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


exception Empty2;;
let rec is_mirror_in_tree word pos factors d = (* checks that the factor of length d at pos is not mirrored in the tree *)
	match factors with
	| Leaf -> if d = 0 then true else raise NonMatchingSize (* not supposed to happen : tree and word are same length/depth *)
	| Nil -> false
	| Node(t1,t2) -> match word.(pos+d-1) with
		| 0 -> is_mirror_in_tree word pos t1 (d-1)
		| 1 -> is_mirror_in_tree word pos t2 (d-1)
		| -1 -> raise Empty2
		| _ ->  raise BadValue
;;



let is_still_alpha_free word n alpha plus =
	let max_alpha = ref ((1,1):rat) in
	for p = 1 to int_of_float ((float_of_int (n+1))/. (float_of_rat alpha)) + 1 do (*p is the tested period, +1 is to be sure*)
		let pos = ref (n-p) in
		let end_of_repetition = ref false in
		while not(!end_of_repetition) && !pos >= 0 do
			if word.(!pos) != word.(!pos+p) then
				end_of_repetition := true
			else
				pos := !pos - 1				
		done;
		max_alpha := max_rat !max_alpha (n-(!pos), p);
	done;
	if plus then (ge alpha (!max_alpha)) (*we must not have repetition of size more than alpha, except alpha itself *)
	else (gt alpha (!max_alpha)) (*we must not have repetition of size alpha (or more) *)
;;

(* Test
Printf.printf "is_still_alpha_free : %b\n" (is_still_alpha_free [|1;0;1;0;1;-1;-1|] 4 (3,1) false);; (*true*) 
Printf.printf "is_still_alpha_free : %b\n" (is_still_alpha_free [|1;0;1;0;1;-1;-1|] 4 (5,2) false);; (*false*) 
*)

exception Sortir0;;
let d_directed_alpha_free d alpha l plus = (*l is maximal length of word we want*)
	let word = Array.make l (-1) in
	let rec aux factors pos =
		for bit=0 to 1 do
			let pos = pos+1 in
			word.(pos) <- bit;
			(*Printf.printf "pos : %d\n" pos;*)
			if pos >= d-1 then (*bit we add will form a new factor*)
			begin 
				(*Printf.printf("adding factor from word :\n");
				print_array word;
				Printf.printf " at pos %d and length %d\n" (pos-d+1) d;*)
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
			word.(pos) <- -1
		done;
	in try aux Nil (-1);
	[| |]
	with Sortir0 -> word
;;

(*
let d = 5	 in
let l = 15 in
let (alpha:rat) = (7,3) in
Printf.printf "%d-directed word of size %d and a-free where a = " d l;
print_rat alpha;
print_array (d_directed_alpha_free d alpha l false);;*)

(*loop for finding first d that has a word d-directed 7/3-free*)
(*
let (alpha:rat) = (7,3) in
let l = 1000 in
let found = ref false in
let d = ref 5 in
let end_word = ref [||] in
while not(!found) do
	Printf.printf "Looking for a word %d-directed of length %d and a+-free with a =%!" (!d) l;
	print_rat alpha;
	let word = (d_directed_alpha_free (!d) alpha l true) in
	if word = [||] then d := !d + 1
	else begin found := true; end_word := word end
done;
Printf.printf "Minimal d found for d-directed word of size %d and a-free where a = " l;
print_rat alpha;
Printf.printf "is  : %d\nAnd word found is : \n" (!d);
print_array !end_word;;
*)
























let print_array_pos arr start stop =
	print_string "[|";
	for i = start to stop do
		print_int arr.(i); print_string ";"
	done;
	print_string "|]"
;;



let is_still_alpha_free word n alpha plus =
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
		(*if plus then begin if gt !max_alpha alpha then begin Printf.printf "factor from below word between pos %d and %d breaks alpha-freeness \n" (!pos) n;
			print_array_pos word (!pos+1) n end end*)
		p := !p + 1
	done;
	!res
;;



exception Sortir3 of (int list list);;
(* l >= d*)
let homomorphism_alpha d l alpha plus = (*Generate by backtracking 3 words d-directed such that any concatenation of them remains d-directed
and satisfies synchronizing, i.e none of them is factor of concatenation of the two others.
--> word of size 3*l satisfying everything*)
	let rec hom_aux current_word prefixes fst_suffix words factors=
		for bit=0 to 1 do
			let new_current_word = bit::current_word in
			if is_still_alpha_free (Array.of_list (List.rev new_current_word)) (List.length new_current_word - 1) alpha plus then
			begin (*else stop backtracking here, useless to continue with alpha-freeness broken*)
				let new_factors = tree_add factors new_current_word d in (*first d-bit is necessary to check in every case*)
				if List.length(current_word) < (d-1) then (*under that, no factor of size d -> nothing to check*)
					hom_aux (bit :: current_word) prefixes fst_suffix words factors
				else
				begin
					if not(is_in_tree (List.rev (isolate_factor new_current_word d)) new_factors) then (*else stop backtracking here*)
					begin
						let words = ref words in
						let fst_suffix = ref fst_suffix in 
						let prefixes = ref prefixes in	
						if d = List.length(new_current_word)  || l+d = List.length(new_current_word) then begin
							prefixes := (List.rev (isolate_factor new_current_word d))::!prefixes
						end;
						(*memorize the suffix of the "first" word of size l finished*)
						if l = List.length(new_current_word) then begin
							fst_suffix := (isolate_factor new_current_word d);
							words := (isolate_factor new_current_word l) :: !words
						end;
						
						(*case end of second word : must check all concat with prefix from first word*)
						if 2*l = List.length(new_current_word) then begin
							words := (isolate_factor new_current_word l)::!words;
							let still_true = ref true in
							let i = ref 1 in
							let new_factors = ref new_factors in
							while !still_true && !i < d do
								let partial_factor = (isolate_factor new_current_word !i) in
								let complementary_prefix = List.rev (isolate_factor (List.hd(List.tl (!prefixes))) (d-(!i))) in 
								(*prefixes contains prefix of first and second word, we access first word that was added first*)
								let factor = List.rev (complementary_prefix @ partial_factor) in (*as always, factor is given in opposite direction*)
								new_factors := tree_add !new_factors factor d;
								if is_in_tree (List.rev factor) !new_factors then
								begin
									still_true := false;
									(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
									Printf.printf "tested factor was :\n";
									print_list (factor);
									Printf.printf "backtrack was tried on :\n";
									print_list (new_current_word);	*)
								end;
								i := !i+1;
							done;
							if !still_true then hom_aux new_current_word !prefixes !fst_suffix !words !new_factors
							(*else stop backtracking here*)
						end
						else begin
							(*case end of third and last word : must check all concat with prefixes from first and second word*)
							if 3*l = List.length(new_current_word) then begin
								words := (isolate_factor new_current_word l)::!words;
								(*Printf.printf "Word of size 3*l reached ! : \n";
								print_list (current_word);
								Printf.printf "words contain :\n";
								print_list_of_list (!words);*)
								let still_true = ref true in
								let new_factors = ref new_factors in
								for prefix=0 to 1 do
									let i = ref 1 in
									while !still_true && !i < d do
										let partial_factor = (isolate_factor new_current_word !i) in
										let complementary_prefix = (if prefix = 0 then (List.rev (isolate_factor (List.hd(List.tl !prefixes)) (d-(!i))))
											else (List.rev (isolate_factor (List.hd(!prefixes)) (d-(!i))))) in 
										(*prefixes contains prefix of first and second word, we access first word that was added first*)
										let factor = complementary_prefix @ partial_factor in (*as always, factor is given in opposite direction*)
										new_factors := tree_add !new_factors factor d;
										if is_in_tree (List.rev factor) !new_factors then
										begin
											still_true := false;
											(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
											Printf.printf "tested factor was :\n";
											print_list (factor);
											Printf.printf "backtrack was tried on words:\n";
											print_list_of_list (!words);*)
										end;
										i := !i+1
									done;
								done;
								if !still_true then begin
									match !words with
									| [l3;l2;l1] -> let w1 = Array.of_list l1 in
										let w2 = Array.of_list l2 in
										let w3 = Array.of_list l3 in
										if is_synchronized w1 w2 w3 l then raise (Sortir3 !words)
										(*else begin
											Printf.printf "Word of size 3*l reached but not synchronized : \n";
											print_list (current_word);
											Printf.printf "words contain :\n";
											print_list_of_list (!words);
										end*)
									| _ -> raise BadValue3 (*not supposed to happen*)
								end
							end
							(*otherwise : not end of a word*)
							else
							begin
								(*case beginning of last word : in this case add a check for every factor made from the end of first suffix*)
								if (2*l+1 <= List.length(new_current_word) && List.length(new_current_word) <= 2*l+d-1) then
								begin
									let partial_length = (List.length(new_current_word) mod l) in
									let partial_factor = (isolate_factor new_current_word partial_length) in
									let complementary_suffix = (isolate_factor (!fst_suffix) (d - partial_length)) in
									let mix_up_factor = partial_factor@complementary_suffix in
									let new_factors = tree_add new_factors mix_up_factor d in
									if not(is_in_tree (List.rev mix_up_factor) new_factors) then
										hom_aux new_current_word !prefixes !fst_suffix !words new_factors
								end
								else
								(*None of the "mean" cases above*)
									hom_aux new_current_word !prefixes !fst_suffix !words new_factors
							end
						end
											
					end
					(*if not(is_not_d_directed_anymore (bit :: word) new_factors d) then*)
				end		(*hom_aux (bit :: word) words new_factors*)
			end
		done;
	in try hom_aux [] [] [] [] Nil;
	[]
	with Sortir3(words) -> List.map List.rev words
;;

(*
let d = 13 in
let l = 13 in
let (alpha:rat) = (7,3) in
Printf.printf "%d-directed homomorphism 7/3+-free of size %d :\n" d l;
print_list_of_list (homomorphism_alpha d l alpha true);;
*)
(*[[1;0;1;1;0;0;1;0;1;1;0;1;1]; [0;1;1;0;0;1;0;1;1;0;1;0;0]; [0;0;1;0;0;1;0;1;1;0;0;1;0]]*)



let thue_morse n =
	let res = Array.make (n+1) (-1) in
	res.(0) <- 0;
	for i = 1 to n do
		let k = (i mod 2) in 
		if k = 0 then res.(i) <- res.(i/2)
		else res.(i) <- 1 - (res.(i/2))
	done;
	res
;;

(* Test
print_array (thue_morse 100);;
*)

let ternaire_sans_carre n =
	let t_m = thue_morse (4*n) in
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

(*Test
print_array (ternaire_sans_carre 100);;
*)

let phi0 i = match i with
	| 0 -> [1;0;1;1;0;0;1;0;1;1;0;1;1]
	| 1 -> [0;1;1;0;0;1;0;1;1;0;1;0;0]
	| 2 -> [0;0;1;0;0;1;0;1;1;0;0;1;0]
	| _ -> raise BadValue
;;

let hom_transform phi n =
	let ternaire = ternaire_sans_carre n in
	 List.concat (List.map phi (Array.to_list ternaire))
;;

(*
print_list (hom_transform 100);;
*)



let is_d_directed_and_alpha_free word d alpha plus =
	let res = ref true in
	let factors = ref Nil in
	let i = ref 0 in
	while !res && !i < Array.length word do
		if !i >= d-1 then
		begin
			factors := tree_add_arr (!factors) word (!i-d+1) d;
			if is_mirror_in_tree word (!i-d+1) (!factors) d then begin
				res := false; (*Printf.printf "Not d-directed\n" *) end;
		end;
		if not(is_still_alpha_free word (!i) alpha plus) then
			begin res := false; (*Printf.printf "Not alpha-free\n"*) end;
		i := !i + 1
	done;
	!res
;;

(* Test
Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free [|0;1;0;1;0|] 5 (3,1) true);; (*false : not 5-directed*)
Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free [|0;1;0;1;1|] 5 (3,1) true);; (*true*)
Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free [|0;1;0;1;0;0|] 6 (5,2) false);; (*false : not 5/2-free*)
Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi0 100)) 13 (7,3) true);;
print_array_pos (Array.of_list (hom_transform phi0 100)) 0 39;;
*)




(*
let homomorphism_alpha d l alpha plus = (*Generate by backtracking 3 words d-directed such that any concatenation of them remains d-directed
and satisfies synchronizing, i.e none of them is factor of concatenation of the two others.
--> word of size 3*l satisfying everything*)
	let rec hom_aux current_word prefixes fst_suffix words factors=
		for bit=0 to 1 do
			let new_current_word = bit::current_word in
			(*Printf.printf "backtrack on word :\n";
			print_list new_current_word;*)
			if is_still_alpha_free (Array.of_list (List.rev new_current_word)) (List.length new_current_word - 1) alpha plus then
			begin (*else stop backtracking here, useless thing*)
				let new_factors = tree_add factors new_current_word d in (*first d-bit is necessary to check in every case*)
				let words = ref words in
				if List.length(current_word) < (d-1) then (*under that, no factor of size d -> nothing to check*)
				begin
					if l = List.length(new_current_word) || 2*l = List.length(new_current_word) then begin
						words := (isolate_factor new_current_word l) :: !words;
					end;
					if 3*l = List.length(new_current_word) then
					begin
						words := (isolate_factor new_current_word l) :: !words;
						match !words with
						| [l1;l2;l3] -> let w1 = Array.of_list l1 in
							let w2 = Array.of_list l2 in
							let w3 = Array.of_list l3 in
							let phi i = match i with
								| 0 -> List.rev l1
								| 1 -> List.rev l2
								| 2 -> List.rev l3
								| _ -> raise BadValue
							in if is_synchronized w1 w2 w3 l && 
							(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi 10)) d alpha plus)
								then raise (Sortir3 !words)
						| _ -> Printf.printf "words contain something else than 3 words :\n";
										print_list new_current_word;
										print_list_of_list !words; raise BadValue3 (*not supposed to happen*)
					end
					else hom_aux (bit :: current_word) prefixes fst_suffix (!words) factors
				end
				else
				begin
					if not(is_in_tree (List.rev (isolate_factor new_current_word d)) new_factors) then (*else stop backtracking here*)
					begin
						let fst_suffix = ref fst_suffix in 
						let prefixes = ref prefixes in	
						if d = List.length(new_current_word)  || l+d = List.length(new_current_word) then begin
							prefixes := (List.rev (isolate_factor new_current_word d))::!prefixes
						end;
						(*memorize the suffix of the "first" word of size l finished*)
						if l = List.length(new_current_word) then begin
							fst_suffix := (isolate_factor new_current_word d);
							words := (isolate_factor new_current_word l) :: !words;
						end;
						
						(*case end of second word : must check all concat with prefix from first word*)
						if 2*l = List.length(new_current_word) then begin
							words := (isolate_factor new_current_word l)::!words;
							let still_true = ref true in
							let i = ref 1 in
							let new_factors = ref new_factors in
							while !still_true && !i < d && l >= d do (* Note : il l < d, don't do these checks, there are
							too many difficult overlapses. Just bruteforce on small things (d-directedness is tested upon returning the word
							at the end anyway, we just don't cut useless branches before reaching this).*)
								let partial_factor = (isolate_factor new_current_word !i) in
								let complementary_prefix = List.rev (isolate_factor (List.hd(List.tl (!prefixes))) (d-(!i))) in 
								(*prefixes contains prefix of first and second word, we access first word that was added first*)
								let factor = List.rev (complementary_prefix @ partial_factor) in (*as always, factor is given in opposite direction*)
								new_factors := tree_add !new_factors factor d;
								if is_in_tree (List.rev factor) !new_factors then
								begin
									still_true := false;
									(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
									Printf.printf "tested factor was :\n";
									print_list (factor);
									Printf.printf "backtrack was tried on :\n";
									print_list (new_current_word);	*)
								end;
								i := !i+1;
							done;
							if !still_true then hom_aux new_current_word !prefixes !fst_suffix !words !new_factors
							(*else stop backtracking here*)
						end
						else begin
							(*case end of third and last word : must check all concat with prefixes from first and second word*)
							if 3*l = List.length(new_current_word) then begin
								words := (isolate_factor new_current_word l)::!words;
								(*Printf.printf "Word of size 3*l reached ! : \n";
								print_list (current_word);
								Printf.printf "words contain :\n";
								print_list_of_list (!words);*)
								let still_true = ref true in
								let new_factors = ref new_factors in
								for prefix=0 to 1 do
									let i = ref 1 in
									while !still_true && !i < d  && l >= d do
										let partial_factor = (isolate_factor new_current_word !i) in
										let complementary_prefix = (if prefix = 0 then (List.rev (isolate_factor (List.hd(List.tl !prefixes)) (d-(!i))))
											else (List.rev (isolate_factor (List.hd(!prefixes)) (d-(!i))))) in 
										(*prefixes contains prefix of first and second word, we access first word that was added first*)
										let factor = complementary_prefix @ partial_factor in (*as always, factor is given in opposite direction*)
										new_factors := tree_add !new_factors factor d;
										if is_in_tree (List.rev factor) !new_factors then
										begin
											still_true := false;
											(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
											Printf.printf "tested factor was :\n";
											print_list (factor);
											Printf.printf "backtrack was tried on words:\n";
											print_list_of_list (!words);*)
										end;
										i := !i+1
									done;
								done;
								if !still_true then begin
									match !words with
									| [l1;l2;l3] -> let w1 = Array.of_list l1 in
										let w2 = Array.of_list l2 in
										let w3 = Array.of_list l3 in
										let phi i = match i with
											| 0 -> List.rev l1
											| 1 -> List.rev l2
											| 2 -> List.rev l3
											| _ -> raise BadValue
										in if is_synchronized w1 w2 w3 l && 
										(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi 10)) d alpha plus)
											then raise (Sortir3 !words)
										(*else begin
											Printf.printf "Word of size 3*l reached but not synchronized : \n";
											print_list (current_word);
											Printf.printf "words contain :\n";
											print_list_of_list (!words);
										end*)
									| _ -> Printf.printf "words contain something else than 3 words :\n";
										print_list new_current_word;
										print_list_of_list !words; raise BadValue3 (*not supposed to happen*)
								end
							end
							(*otherwise : not end of a word*)
							else
							begin
								(*case beginning of last word : in this case add a check for every factor made from the end of first suffix*)
								if (2*l+1 <= List.length(new_current_word) && List.length(new_current_word) <= 2*l+d-1 && l >= d) then
								begin
									let partial_length = (List.length(new_current_word) mod l) in
									let partial_factor = (isolate_factor new_current_word partial_length) in
									let complementary_suffix = (isolate_factor (!fst_suffix) (d - partial_length)) in
									let mix_up_factor = partial_factor@complementary_suffix in
									let new_factors = tree_add new_factors mix_up_factor d in
									if not(is_in_tree (List.rev mix_up_factor) new_factors) then
										hom_aux new_current_word !prefixes !fst_suffix !words new_factors
								end
								else
								(*None of the "mean" cases above*)
									hom_aux new_current_word !prefixes !fst_suffix !words new_factors
							end
						end
											
					end
					(*if not(is_not_d_directed_anymore (bit :: word) new_factors d) then*)
				end		(*hom_aux (bit :: word) words new_factors*)
			end
		done;
	in try hom_aux [] [] [] [] Nil;
	[]
	with Sortir3(words) -> List.map List.rev words
;;


for l = 3 to 13 do
	let d = 13 in
	(*let l = 13 in*)
	let (alpha:rat) = (7,3) in
	Printf.printf "%d-directed homomorphism 7/3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true);
done;;*)


let is_still_alpha_free_verbose word n alpha plus =
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
		if plus && (gt !max_alpha alpha) then  begin
			res := false; (*we must not have repetition of size more than alpha, except alpha itself *)
			Printf.printf "factor from below word between pos %d and %d breaks alpha-freeness \n" (!pos +1) n;
			print_array_pos word (!pos+1) n;
			print_string "\n"
		end
		else if (not plus) && ge !max_alpha alpha then begin
			res := false; (*we must not have repetition of size alpha (or more) *)
		end;
		p := !p + 1
	done;
	!res
;;


let is_alpha_free word alpha plus =
	let res = ref true in
	let i = ref 0 in
	while !res && !i < Array.length word do
		if not(is_still_alpha_free word (!i) alpha plus) then
			begin res := false; (*Printf.printf "Not alpha-free because of suffix at %d\n" (!i)*) end;
		i := !i + 1
	done;
	!res
;;

let stays_alpha_free l1 l2 l3 alpha plus =
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

(* l >= d*)
let homomorphism_alpha d l alpha plus = (*Generate by backtracking 3 words d-directed such that any concatenation of them remains d-directed
and satisfies synchronizing, i.e none of them is factor of concatenation of the two others.
--> word of size 3*l satisfying everything*)
	let rec hom_aux current_word prefixes fst_suffix words factors=
		for bit=0 to 1 do
			let new_current_word = bit::current_word in
			if is_still_alpha_free (Array.of_list (List.rev new_current_word)) (List.length new_current_word - 1) alpha plus then
			begin (*else stop backtracking here, useless to continue with alpha-freeness broken*)
			
				let new_factors = tree_add factors new_current_word d in (*first d-bit is necessary to check in every case*)
				if List.length(current_word) < (d-1) then (*under that, no factor of size d -> nothing to check*)
					hom_aux (bit :: current_word) prefixes fst_suffix words factors
				else
				begin
					if not(is_in_tree (List.rev (isolate_factor new_current_word d)) new_factors) then (*else stop backtracking here*)
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
						(*case end of second word : must check all concat with prefix from first word*)
						if 2*l = List.length(new_current_word) then begin
							(*print_string "word of size 2*l reached !\n";*)
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
								begin
									still_true := false;
									(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
									Printf.printf "tested factor was :\n";
									print_list (factor);
									Printf.printf "backtrack was tried on :\n";
									print_list (new_current_word);	*)
								end;
								i := !i+1;
							done;
							if !still_true then
							begin
								begin match !words with
									| [l2;l1] -> still_true := is_alpha_free (Array.of_list ((List.rev l2)@(List.rev l1))) alpha plus;
									| _ -> raise BadValue3 (*not supposed to happen*);
								end;
								if !still_true then
									hom_aux new_current_word !prefixes !fst_suffix !words !new_factors
								(*else begin
									Printf.printf "correct word of size 2*l reached for d-directedness but is not alpha+-free :\n";
									print_list_of_list (List.map List.rev (!words))
								end;*)
							end;
							(*else stop backtracking here*)
						end
						else begin
							
							(*************************************************************************************************)
							(*case end of third and last word : must check all concat with prefixes from first and second word*)
							if 3*l = List.length(new_current_word) then begin
								words := (isolate_factor new_current_word l)::!words;
								let still_true = ref true in
								let new_factors = ref new_factors in
								
								(*checking that adding a beginning of prefix from first 2 words preserves d-directedness*)
								for prefix=0 to 1 do
									(*Printf.printf "prefix %d current word is: \n" prefix;
									print_list new_current_word;
									Printf.printf "prefixes are : \n";
									print_list_of_list (!prefixes);*)
									let i = ref 1 in
									while !still_true && !i < d do
										let partial_factor = List.rev (isolate_factor new_current_word !i) in
										let complementary_prefix = (if prefix = 0 then ((isolate_factor (List.hd(List.tl !prefixes)) (d-(!i))))
											else ((isolate_factor (List.hd(!prefixes)) (d-(!i))))) in 
										(*prefixes contains prefix of first and second word, we access first word that was added first*)
										let factor = List.rev (partial_factor @ complementary_prefix)  in (*as always, factor is given in opposite direction*)
										(*Printf.printf "new factor tested in crossover is : \n";
										print_list factor;*)
										new_factors := tree_add !new_factors factor d;
										if is_in_tree (List.rev factor) !new_factors then
										begin
											still_true := false;
											(*Printf.printf "factor's reverse is already in tree : reverse backtracking\n";
											Printf.printf "tested factor was :\n";
											print_list (factor);
											Printf.printf "backtrack was tried on words:\n";
											print_list_of_list (!words);*)
										end;
										i := !i+1
									done;
								done;
								
								(* Now we have three perfectly d-directed words, need to check alpha-freeness is also preserved by permutations *)
								if !still_true then begin
									(*Printf.printf "Word of size 3*l and d-directed in every way reached ! : \n";
									print_list_of_list (List.map List.rev (!words));*)
									match !words with
									| [l3;l2;l1] -> let ll1 = List.rev l1 in
										let ll2 = List.rev l2 in
										let ll3 = List.rev l3 in
										(*print_list ll1;
										print_list ll2;
										print_list ll3;*)
										if not(ll1 = ll2) && not(ll1 = ll3) && not(ll2 = ll3) && 
										stays_alpha_free ll1 ll2 ll3 alpha plus then raise (Sortir3 !words)
									(*let w1 = Array.of_list l1 in
										let w2 = Array.of_list l2 in
										let w3 = Array.of_list l3 in
										let phi i = match i with
											| 0 -> List.rev l1
											| 1 -> List.rev l2
											| 2 -> List.rev l3
											| _ -> raise BadValue
										in if (*is_synchronized w1 w2 w3 l && *) (*TODO : put this back on ?*)
										(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi 10)) d alpha plus)
											then  raise (Sortir3 !words)*)
										(*else begin
											Printf.printf "Word of size 3*l reached but not synchronized : \n";
											print_list (current_word);
											Printf.printf "words contain :\n";
											print_list_of_list (!words);
										end*)
									| _ -> raise BadValue3 (*not supposed to happen*)
								end
							end
							(*otherwise : not end of a word*)
							else
							begin
							
								(**********************************************************************************************************)
								(*case beginning of last word : in this case add a check for every factor made from the end of first suffix*)
								if (2*l+1 <= List.length(new_current_word) && List.length(new_current_word) <= 2*l+d-1) then
								begin
									let partial_length = (List.length(new_current_word) mod l) in
									let partial_factor = (isolate_factor new_current_word partial_length) in
									let complementary_suffix = (isolate_factor (!fst_suffix) (d - partial_length)) in
									let mix_up_factor = partial_factor@complementary_suffix in
									let new_factors = tree_add new_factors mix_up_factor d in
									if not(is_in_tree (List.rev mix_up_factor) new_factors) then
										hom_aux new_current_word !prefixes !fst_suffix !words new_factors
								end
								else
																
								(********************************)
								(*None of the "mean" cases above*)
									hom_aux new_current_word !prefixes !fst_suffix !words new_factors
							end
						end
											
					end
					(*if not(is_not_d_directed_anymore (bit :: word) new_factors d) then*)
				end		(*hom_aux (bit :: word) words new_factors*)
			end
		done;
	in try hom_aux [] [] [] [] Nil;
	[]
	with Sortir3(words) -> List.map List.rev words
;;

(*print_array (d_directed_alpha_free 6 (3,1) 1000 true);;*)


(* TESTS for d=6, alpha = 3 --> IT WORKS !*)
(*
for l = 6 to 15 do
	let d = 6 in
	let (alpha:rat) = (3,1) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;

let phi6 i = match i with
	| 0 -> [0;1;0;1;1;0;0;1;0;1;1;1;0]
	| 1 -> [0;1;0;1;1;0;0;0;1;0;1;1;0]
	| 2 -> [0;0;1;0;1;0;1;1;1;0;0;0;1]
	| _ -> raise BadValue
;;

Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi6 100)) 6 (3,1) true);;
*)

(*TESTS for d = 8, alpha = 8/3 --> WOOOOORKS AGAIN ! (minimal size of image 30)*)
(*
for l = 16 to 30 do
	let d = 8 in
	let (alpha:rat) = (8,3) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;

let phi8 i = match i with
	| 0 -> [0;1;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1]
	| 1 -> [0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1;0;1;1;0;0;1;0;0;1;0;1;1]
	| 2 -> [0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi8 100)) 8 (8,3) true);;
*)

(* TESTS : Still works :*)
(*
for l = 10 to 30 do
	let d = 10 in
	let (alpha:rat) = (5,2) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;

let phi10 i = match i with
	| 0 -> [0;0;1;0;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;0;1;1;0;0;1;1]
	| 1 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;1;0;0;1;0;1;1;0;1;0;1;1]
	| 2 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi10 100)) 10 (5,2) true);;
*)

(*
for l = 61 to 70 do
	let d = 13 in
	let (alpha:rat) = (7,3) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;
*)

let phi13 i = match i with
	| 0 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 1 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 2 -> [0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "is_d_directed_and_alpha_free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi13 100)) 13 (7,3) true);;

(*print_array (Array.of_list (hom_transform phi13 100));;*)


Printf.printf "is synchronized : %b\n" (is_synchronized (Array.of_list (phi13 0)) (Array.of_list (phi13 1)) (Array.of_list (phi13 2)) 62);;





















let print_list_as_word l =
	let rec print_elements = function
		| [] -> ()
		| h::t -> print_int h; print_elements t
	in
	print_elements l;
;;

(*
let word = (d_directed_alpha_free 13 (7,3) 20000 true);;

let dico = [| [|0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0|];
[|1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0|];
[|0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1|];
[|0;0;1;1;0;1;1;0;0;1;0;1;1|];
[|0;1;0;0;1;0;1;1;0|];
[|1;0;0;1;0;1;1;0|];
[|0;0;1;0;0;1|];
[|0;1;1;0;1|] |];;

let l = ref [] in
let i = ref 0 in
while !i < Array.length word - 20 do
	let found = ref false in
	let j = ref 0 in
	while (!j) <= 7 && not(!found) do
		if Array.sub word (!i) (Array.length (dico.(!j))) = dico.(!j) then
		begin
			l := (!j) :: (!l);
			found := true
		end;
		j := !j + 1
	done;
	i := !i + Array.length dico.(List.hd (!l));
done;
print_list_as_word (List.rev (!l));;
*)







(*
let inter (r1 : rat) (r2:rat) = match r1, r2 with
	|(p,q), (p',q') -> (p+p', q+q')
;;

let rat_minus (r1 : rat) (r2:rat) = match r1,r2 with
	|(p,q), (p',q') -> (p*q'-p'*q, q*q')
;;

let (alpha_min : rat ref) = ref (3,1) in
let (alpha_max : rat ref) = ref (4,1) in

let found = ref false in
while not(!found) && ge (rat_minus (!alpha_max) (!alpha_min)) (1,100) do
	let alpha_inter = inter (!alpha_min) (!alpha_max) in
	(*print_string "Testing : \n";
	print_rat alpha_inter;*)
	let w = (d_directed_alpha_free 5 (alpha_inter) 1000 false) in
	let w_plus = (d_directed_alpha_free 5 (alpha_inter) 1000 true) in
	if w = [||] && w_plus != [||] then begin
		print_string "result found for alpha = \n";
		print_rat (alpha_inter);
		found := true
	end
	else begin
		if w_plus = [||] then alpha_min := alpha_inter
		else alpha_max := alpha_inter
	end
done;

print_rat (!alpha_min);
print_rat (!alpha_max);;

print_array (d_directed_alpha_free 5 (5,1) 1000 true)*)






