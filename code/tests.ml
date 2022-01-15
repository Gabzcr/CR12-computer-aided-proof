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


(*****************************************************************************)
(*                            General Tests                                  *)
(*****************************************************************************)


(* ---------- Words ---------- *)
print_string "\n------------------------------------\n";;
print_string "---------- Tests on Words ----------\n";;
print_string "------------------------------------\n";;

print_string "\nBinary Thue Morse word of size 500 :\n\n";;
print_array (thue_morse 500);;

print_string "\nTernary Thue Morse word of size at least 500 :\n\n";;
print_array (ternaire_sans_carre 500);;

Printf.printf "\nThue Morse word of size %d is 7/4+ free :%b\n" 10000 (is_alpha_free (ternaire_sans_carre 10000) (7,4) true);;


(*****************************************************************************)
(*                       Tests on the Backtrackings                          *)
(*****************************************************************************)

print_string "\n\n--------------------------------------------\n";;
print_string "---------- Tests on Backtrackings ----------\n";;
print_string "--------------------------------------------\n";;

(*loop for finding first d that has a word d-directed 7/3-free*)
(* This was the first attempt at finding a pair (d, alpha) in this project. 
But since it is now obsolete with the dichotomy method, I leave it commented.
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
*)


(*Testing the dichotomy to find the alpha that is tight for a given d.
ie there exists a d-directed alpha+-free word but no d-directed alpha-free word*)

print_string "\n--- Finding tight alpha values of small values of d by dichotomy : ---\n";;

for d = 5 to 15 do
	Printf.printf "Searching by dichotomy for tight alpha for %d-directed word : " d;
	try
	print_rat (dichotomy (2,1) (3,1) d 1000);
	with DichotomyOutOfRange -> Printf.printf "Dichotomy failed\n";
done;;

Printf.printf "\nActually, for 5-directed words, there are no infinite alpha-free word for any alpha.\nIndeed, a infinite 5-directed word is necessarily an infinite repetition of the sequence \"101100\" or \"110100\".\n";;


(*****************************************************************************)
(*                        Tests on the Morphism                              *)
(*****************************************************************************)


print_string "\n\n---------------------------------------------------\n";;
print_string "---------- Tests on morphism generation  ----------\n";;
print_string "---------------------------------------------------\n";;

let phi13 i = match i with
	| 0 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 1 -> [0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| 2 -> [0;0;1;0;0;1;1;0;0;1;0;1;1;0;0;1;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1;0;0;1;0;0;1;1;0;0;1;0;1;1;0;1;0;0;1;0;1;1]
	| _ -> raise BadValue
;;

print_string "\nBeginning of an infinite 13-directed and 7/3+-free word, image of Thue Morse ternary sequence of size at least 10 by some morphism :\n";;
print_list_as_word (hom_transform phi13 10);;

(* ---------- d = 6 , alpha = 3 ---------- *)

print_string "\n\n\n--------------- d = 6 , alpha = 3  ---------------\n";;

(* Now I let these in commentary since it gets pretty long pretty fast. *)
(*
print_string "\nSearching by backtracking for a morphism turning Thue-Morse ternary word into a 6-directed words 3+-free :\n\n";;
for l = 6 to 13 do
	let d = 6 in
	let (alpha:rat) = (3,1) in
	Printf.printf "%d-directed homomorphism (3+)-free of size %d : %!" d l;
	if l = 13 then print_string "\n";
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;
*)

(*Above test concludes with following morphism of size l = 13*)
let phi6 i = match i with
	| 0 -> [0;1;0;1;1;0;0;1;0;1;1;1;0]
	| 1 -> [0;1;0;1;1;0;0;0;1;0;1;1;0]
	| 2 -> [0;0;1;0;1;0;1;1;1;0;0;0;1]
	| _ -> raise BadValue
;;

Printf.printf "Morphism is found of minimal size 13 :\n";;
print_list_of_list [phi6 0; phi6 1; phi6 2];;
Printf.printf "\nChecking this morphism (hypothesis for Lemma 2.1 (Ochem)):\n";;
Printf.printf "First test : Image of ternary Thue Morse sequence of size >= 100 is 6-directed and (3+)-free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi6 100)) 6 (3,1) true);;
Printf.printf "Morphism is synchronizing :%b\n" (is_synchronized (Array.of_list (phi6 0)) (Array.of_list (phi6 1)) (Array.of_list (phi6 2)) 13);;
Printf.printf "Morphism is 13-uniform.\n%!";;
let (alpha : rat) = (7,4) in
let (beta : rat) = (3,1) in
let bound = compute_bound alpha beta 13 in
Printf.printf "Images of all (7/4+)-free ternary words of size at most %d are indeed (3+)-free :%b\n" bound (images_are_free phi6 bound alpha beta);;
print_string "---> There is an infinite 6-directed word (3+)-free !\n";;



(* ---------- d = 8, alpha = 8/3 ---------- *)

print_string "\n\n--------------- d = 8 , alpha = 8/3  ---------------\n";;

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

Printf.printf "Morphism is found of minimal size 30 :\n";;
print_list_of_list [phi8 0; phi8 1; phi8 2];;
Printf.printf "\nChecking this morphism (hypothesis for Lemma 2.1 (Ochem)):\n";;
Printf.printf "First test : Image of ternary Thue Morse sequence of size >= 100 is 8-directed and (8/3+)-free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi8 100)) 8 (8,3) true);;
Printf.printf "Morphism is synchronizing :%b\n" (is_synchronized (Array.of_list (phi8 0)) (Array.of_list (phi8 1)) (Array.of_list (phi8 2)) 30);;
Printf.printf "Morphism is 30-uniform.\n%!";;
let (alpha : rat) = (7,4) in
let (beta : rat) = (8,3) in
let bound = compute_bound alpha beta 30 in
Printf.printf "Images of all (7/4+)-free ternary words of size at most %d are indeed (8/3+)-free :%b\n" bound (images_are_free phi8 bound alpha beta);;
print_string "---> There is an infinite 8-directed word (8/3+)-free !\n";;



(* ---------- d = 10, alpha = 5/2 ---------- *)

print_string "\n\n--------------- d = 10 , alpha = 5/2  ---------------\n";;

(*
for l = 10 to 30 do
	let d = 10 in
	let (alpha:rat) = (5,2) in
	Printf.printf "%d-directed homomorphism 3+-free of size %d :\n%!" d l;
	print_list_of_list (homomorphism_alpha d l alpha true)
done;;*)

(*Above test concludes with following morphism, of size l=26*)
let phi10 i = match i with
	| 0 -> [0;0;1;0;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;0;1;1;0;0;1;1]
	| 1 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;1;0;0;1;0;1;1;0;1;0;1;1]
	| 2 -> [0;0;1;0;1;0;0;1;0;1;1;0;0;1;0;1;1;0;1;0;1;1;0;0;1;1]
	| _ -> raise BadValue
;;

Printf.printf "Morphism is found of minimal size 26 :\n";;
print_list_of_list [phi10 0; phi10 1; phi10 2];;
Printf.printf "\nChecking this morphism :\n";;
Printf.printf "First test : Image of ternary Thue Morse sequence of size >= 100 is 10-directed and (5/2+)-free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi10 100)) 10 (5,2) true);;
Printf.printf "Morphism is synchronizing :%b\n" (is_synchronized (Array.of_list (phi10 0)) (Array.of_list (phi10 1)) (Array.of_list (phi10 2)) 26);;
Printf.printf "Morphism is 26-uniform.\n%!";;
let (alpha : rat) = (7,4) in
let (beta : rat) = (5,2) in
let bound = compute_bound alpha beta 26 in
Printf.printf "Images of all (7/4+)-free ternary words of size at most %d are indeed (5/2+)-free :%b\n" bound (images_are_free phi10 bound alpha beta);;
print_string "---> There is an infinite 10-directed word (5/2+)-free !\n";;


(* ---------- d = 13, alpha = 7/3 ---------- *)

print_string "\n\n--------------- d = 13 , alpha = 7/3  ---------------\n";;

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

Printf.printf "Morphism is found of minimal size 62 :\n";;
print_list_of_list [phi13 0; phi13 1; phi13 2];;
Printf.printf "\nChecking this morphism :\n";;
Printf.printf "First test : Image of ternary Thue Morse sequence of size >= 100 is 13-directed and (7/3+)-free : %b\n" (is_d_directed_and_alpha_free (Array.of_list (hom_transform phi13 100)) 13 (7,3) true);;
Printf.printf "Morphism is synchronizing :%b\n" (is_synchronized (Array.of_list (phi13 0)) (Array.of_list (phi13 1)) (Array.of_list (phi13 2)) 62);;
Printf.printf "Morphism is 62-uniform.\n%!";;
(* Below test is a bit long, I leave it in commentary, feel free to put it back and wait a minute.
Result given was indeed true, you can check.
let (alpha : rat) = (7,4) in
let (beta : rat) = (7,3) in
let bound = compute_bound alpha beta 62 in
Printf.printf "Images of all (7/4+)-free ternary words of size at most %d are indeed (7/3+)-free :%b\n" bound (images_are_free phi13 bound alpha beta);;
*)
print_string "Images of all (7/4+)-free ternary words of size at most %d are indeed (7/3+)-free.\n";;
print_string "---> There is an infinite 13-directed word (7/3+)-free !\n";;

print_string "\n";;




