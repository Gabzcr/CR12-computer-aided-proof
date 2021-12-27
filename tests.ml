open Words;;

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

let print_list l =
	let rec print_elements = function
		| [] -> ()
		| [a] -> print_int a
		| h::t -> print_int h; print_string ";"; print_elements t
	in
	print_string "[";
	print_elements l;
	print_string "]\n"
;;

let print_list_as_word l =
	let rec print_elements = function
		| [] -> ()
		| h::t -> print_int h; print_elements t
	in
	print_elements l;
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



(*****************************************************************************)
(*                            General Tests                                  *)
(*****************************************************************************)


(* ---------- Words ---------- *)
print_string "\n------------------------------------\n";;
print_string "---------- Tests on Words ----------\n";;
print_string "------------------------------------\n";;

(*print_string "\nIsolating factor of size 3 from word = [0;1;1;0;0;1] :\n";;
print_list (isolate_factor [0;1;1;0;0;1] 3);;*)
(*This test only tested correction of intermediate functions --> not interesting.*)

print_string "\nBinary Thue Morse word of size 500 :\n\n";;
print_array (thue_morse 500);;

print_string "\n\nTernary Thue Morse word of size at least 500 :\n\n";;
print_array (ternaire_sans_carre 500);;


(* ---------- Binary Trees ---------- *)
(*
print_string "\n\n\n----------------------------------------------------\n";;
print_string "---------- Tests on binary tree structure ----------\n";;
print_string "----------------------------------------------------\n";;

print_string "\nPrinting a simple tree :\n";;
print_tree(Node(Leaf,Nil));;
Printf.printf "\n";;

print_string "\nAdding word [0;1;1;0;0] in Nil tree :\n";;
let t = tree_add Nil [0;1;1;0;0] 5;;
print_tree(t);;
Printf.printf "\n";;

print_string "Adding word [0;1;1;1;0] in previous tree :\n";;
let  t2 = tree_add t [0;1;1;1;0] 6;;
print_tree(t2);;
Printf.printf "\n";;

print_string "\nTesting if word [0;1;1;0;0] is in tree (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil))) (it should)";;
Printf.printf "is_in_tree :%b\n" (is_in_tree [0;1;1;0;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*true*)
print_string "Testing if word [0;1;1;1;0] is in tree (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil))) (it should)";;
Printf.printf "is_in_tree :%b\n" (is_in_tree [0;1;1;1;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*true*)
print_string "Testing if word [0;1;1;1;0] is in tree (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil))) (it shouldn't)";;
Printf.printf "is_in_tree :%b\n" (is_in_tree [0;1;0;1;0] (Node(Node(Nil,Node(Nil,Node(Node(Leaf,Nil),Node(Leaf,Nil)))),Nil)));; (*false*)
*)
(*This section only tested correction of intermediate functions --> not interesting.*)


(* ---------- Directedness and freeness tests ---------- *)
(*
print_string "\n\n\n--------------------------------------------------------\n";;
print_string "---------- Tests on directedness and freeness ----------\n";;
print_string "--------------------------------------------------------\n";;

print_string "\nTesting if word [0;1;1;0;0] is 3-directed (it should not) : ";;
Printf.printf "%b\n" (is_d_directed [0;1;1;0;0] 3);; (*false*)
print_string "Testing if word [1;0;1] is 3-directed (it should not) : ";;
Printf.printf "%b\n" (is_d_directed [1;0;1] 3);; (*false*)
print_string "Testing if word [1;0;0] is 3-directed (it should) : ";;
Printf.printf "%b\n" (is_d_directed [1;0;0] 3);; (*true*)
print_string "Testing if word (d_directed 6 100) is 6-directed (it should) : ";;
Printf.printf "%b\n" (is_d_directed (d_directed 6 100) 6);; (*true*)

print_string "\nTesting if the set of words [| 1;2;3 |] [| 4;5;1 |] [| 2;3;6 |] is synchronized (it should not): ";;
Printf.printf "%b\n" (is_synchronized [| 1;2;3 |] [| 4;5;1 |] [|2;3;6 |] 3);; (*false*)
print_string "Testing if the set of words [| 1;2;3 |] [| 4;5;6 |] [| 2;3;6 |] is synchronized (it should): ";;
Printf.printf "%b\n" (is_synchronized [| 1;2;3 |] [| 4;5;6 |] [| 2;3;6 |] 3);; (*true*)

print_string "\nTesting if the prefix of [|1;0;1;0;1;-1;-1|] of size 4 is still 3-free after adding last letter (it should): ";;
Printf.printf "%b\n" (is_still_alpha_free [|1;0;1;0;1;-1;-1|] 4 (3,1) false);; (*true*)
print_string "Testing if the prefix of [|1;0;1;0;1;-1;-1|] of size 4 is still 5/2-free after adding last letter (it should not): ";;
Printf.printf "%b\n" (is_still_alpha_free [|1;0;1;0;1;-1;-1|] 4 (5,2) false);; (*false*) 

print_string "\nTesting if word [|0;1;0;1;0|] is 5-directed and 3-free (it should not : not 5-directed): ";;
Printf.printf "%b\n" (is_d_directed_and_alpha_free [|0;1;0;1;0|] 5 (3,1) true);; (*false : not 5-directed*)
print_string "Testing if word [|0;1;0;1;1|] is 5-directed and 3-free (it should): ";;
Printf.printf "%b\n" (is_d_directed_and_alpha_free [|0;1;0;1;1|] 5 (3,1) true);; (*true*)
print_string "Testing if word [|0;1;0;1;0;0|]  is 6-directed and 5/2-free (it should not : not 5/2-free): ";;
Printf.printf "%b\n" (is_d_directed_and_alpha_free [|0;1;0;1;0;0|] 6 (5,2) false);; (*false : not 5/2-free*)
*)
(*This section only tested correction of intermediate functions --> not interesting.*)



(*****************************************************************************)
(*                       Tests on the Backtrackings                          *)
(*****************************************************************************)

print_string "\n\n--------------------------------------------\n";;
print_string "---------- Tests on Backtrackings ----------\n";;
print_string "--------------------------------------------\n";;

print_string "\nSearching for a 5-directed word of size 100 :\n\n";;
print_list (d_directed 5 100);;


print_string "\n\nSearching for a 15-directed word 7/3+-free of size 200 :\n\n";;
print_array (d_directed_alpha_free 13 (7,3) 200 true);;


(*loop for finding first d that has a word d-directed 7/3-free*)
print_string "\n\nLooping to find the first d such that there exists a d-directed word 7/3+-free of size 200 :\n\n";;
let exists_d_directed alpha l =
	let found = ref false in
	let d = ref 5 in (*there are no infinite 4-directed words or less than 4. Useless to check them.*)
	let end_word = ref [||] in
	while not(!found) do
		Printf.printf "Looking for %d-directed word 7/3+-free of size %d :\n" (!d) l;
		let word = (d_directed_alpha_free (!d) alpha l true) in
		if word = [||] then begin d := !d + 1; print_string "No such word.\n" end
		else begin found := true; end_word := word end
	done;
	Printf.printf "Minimal d is found. It is %d, and generated word is :\n" (!d);
	print_array !end_word;;

let (alpha:rat) = (7,3) in
let l = 200 in
exists_d_directed alpha l;;


(*Testing the dichotomy to find the alpha that is tight for a given d.
ie there exists a d-directed alpha+-free word but no d-directed alpha-free word*)

print_string "\n";
for d = 5 to 13 do
	Printf.printf "Searching by dichotomy for tight alpha for %d-directed word : " d;
	try
	print_rat (dichotomy (2,1) (3,1) d 1000);
	with DichotomyOutOfRange -> Printf.printf "Dichotomy failed\n";
done;;

Printf.printf "\nActually, for 5-directed words, there are no infinite alpha-free word for any alpha.\nIndeed, a infinite 5-directed word is necessarily an infinite repetition of the sequence \"101100\" or \"110100\".";;


(*****************************************************************************)
(*                        Tests on the Morphism                              *)
(*****************************************************************************)


(* ---------- d = 6 , alpha = 3 ---------- *)

print_string "\n\n---------------------------------------------------\n";;
print_string "---------- Tests on morphism generation  ----------\n";;
print_string "---------------------------------------------------\n";;

print_string "\nSearching by backtracking for a morphism turning Thue-Morse ternary word into a 6-directed words 3+-free :\n\n";;
for l = 6 to 13 do
	let d = 6 in
	let (alpha:rat) = (3,1) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;

(*Above test concludes with following morphism of size l = 13*)
let phi6 i = match i with
	| 0 -> [0;1;0;1;1;0;0;1;0;1;1;1;0]
	| 1 -> [0;1;0;1;1;0;0;0;1;0;1;1;0]
	| 2 -> [0;0;1;0;1;0;1;1;1;0;0;0;1]
	| _ -> raise BadValue
;;

Printf.printf "\nChecking that image of ternary Thue Morse word of size >= 100 by previous morphism is 6-directed and 3+-free : %b"
(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi6 100)) 6 (3,1) true);;


(* ---------- d = 8, alpha = 8/3 ---------- *)
(* Now I let this in commentary since it will get pretty long pretty fast. *)
(*
for l = 16 to 30 do
	let d = 8 in
	let (alpha:rat) = (8,3) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;*)

(*Above test concludes with following morphism of size l = 30*)
let phi8 i = match i with
	| 0 -> [0;1;1;0;0;1;0;0;1;0;1;1;0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1]
	| 1 -> [0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1;0;1;1;0;0;1;0;0;1;0;1;1]
	| 2 -> [0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;0;1;0;1;1;0;1;1;0;0;1;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "\nChecking image obtained for 8-directedness and 8/3+-freeness : %b"
(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi8 100)) 8 (8,3) true);;


(* ---------- d = 10, alpha = 5/2 ---------- *)
(*
for l = 10 to 30 do
	let d = 10 in
	let (alpha:rat) = (5,2) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;*)

(*Above test concludes with following morphism*)
let phi10 i = match i with
	| 0 -> [0;0;1;0;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;0;1;1;0;0;1;1]
	| 1 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;1;0;0;1;0;1;1;0;1;0;1;1]
	| 2 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "\nChecking image obtained for 10-directedness and 5/2+-freeness : %b"
 (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi10 100)) 10 (5,2) true);;


(* ---------- d = 13, alpha = 7/3 ---------- *)

(*
for l = 61 to 70 do
	let d = 13 in
	let (alpha:rat) = (7,3) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;
*)

(*Above test concludes with following morphism of minimal size = 62*)
let phi13 i = match i with
	| 0 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 1 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 2 -> [0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf  "\nChecking image obtained for 13-directedness and 7/3+-freeness : %b"
(is_d_directed_and_alpha_free (Array.of_list (hom_transform phi13 100)) 13 (7,3) true);;


Printf.printf  "\n\nChecking that word obtained from morphism for 13-directedness and 7/3+-freeness is also synchronizing : %b\n"
(is_synchronized (Array.of_list (phi13 0)) (Array.of_list (phi13 1)) (Array.of_list (phi13 2)) 62);;

print_string "\n\nBeginning of an infinite 13-directed and 7/3+-free word, image of Thue Morse ternary sequence of size at least 20 by morphism :\n";;
print_list_as_word (hom_transform phi13 20);;
print_string "\n\n";;


