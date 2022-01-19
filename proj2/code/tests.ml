open Reduction;;

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


(*****************************************************************************)
(*                                  TESTS                                    *)
(*****************************************************************************)


(* Searching for forbidden factors *)
(*
for nb_steps = 2 to 10 do
	let forbid = wrong_factors nb_steps 20 in
	Printf.printf "%!";
	print_tree_as_factors forbid;
	print_string "\n";
	Printf.printf "We forbid %d factors with this method\n" (nb_of_factors_in_tree forbid);
	print_array (generate_no_big_square forbid 1000 (1,3));
done;;
*)



let size = 18 in
let nb_reduc = 5 in
Printf.printf "Creating forbidden factors of size at most %d for at most %d reduction steps.\n" size nb_reduc;
let forbid = wrong_factors 5 18 in
(*print_tree_as_factors forbid;
print_list_of_list (tree_to_list_of_factors forbid);*)
Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
Printf.printf "Trying to generate a word of size 1000 avoiding all these factors :%!\n";
print_array (generate forbid 1000 (1,3));
Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.\n"








