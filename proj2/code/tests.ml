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
	in aux t [];
	print_string "|]\n"
;;


(*****************************************************************************)
(*                                  TESTS                                    *)
(*****************************************************************************)


(* For tests : Word reducible in three steps.
0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1
0;0;0;0;0;1;0;0;1;1;0;0;0;0;0;1;1        (-2)
0;0;0;0;0;1;1;0;0;0;0;0;1;1       (-3)
0;0;0;0;0;1;1        (-7)
*)

if (Array.length Sys.argv) <= 1 then begin (* demo ! *)
	Printf.printf "Creating forbidden factors of variable size for at most %d reduction steps.\n" 6;
	let forbid = wrong_factors 6 [| 0;0;28;26;26;26;26|] (1,3) in
	Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
	Printf.printf "Trying to generate a word of size 1000 avoiding all these factors :%!\n";
	print_array (generate forbid 1000 (1,3));
	Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.%!\n";
end
else begin (* Tests on variable sizes for factors with different number of reduction steps. *)
	let alpha = (int_of_string Sys.argv.(1), int_of_string Sys.argv.(2)) in
	let nb_reduc = int_of_string Sys.argv.(3) in
	let max_sizes = Array.make (nb_reduc+2) 0 in (*Useless number of reduction steps : 0 and 1. Never read. *)
	for i = 2 to nb_reduc do
		max_sizes.(i) <- (int_of_string Sys.argv.(i+2));
	done;
	Printf.printf "Creating forbidden factors of variable size for at most %d reduction steps.\n" nb_reduc;
	let forbid = wrong_factors nb_reduc max_sizes alpha in
	Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
	Printf.printf "Trying to generate a word of size 1000 avoiding all these factors :%!\n";
	print_array (generate forbid 1000 alpha);
	Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.%!\n";
end
;;

(* Test on same size for all factors of any number of reduction steps. Uncomment if you want this test instead. *)
(*
let size = int_of_string (Sys.argv.(1)) in
let nb_reduc = int_of_string (Sys.argv.(2)) in
let alpha = (int_of_string (Sys.argv.(3)), int_of_string (Sys.argv.(4)))in
Printf.printf "Creating forbidden factors of size at most %d for at most %d reduction steps.\n" size nb_reduc;
let forbid = wrong_factors nb_reduc [|size;size;size;size;size;size;size;size|] alpha in
Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
Printf.printf "Trying to generate a word of size 1000 avoiding all these factors :%!\n";
print_array (generate forbid 1000 alpha);
Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.%!\n";;
*)



(*------------------RESULTAT------------------------*)
(*
Factors of size 20 and maximum 5 reduction steps are enough to prove bound 2/5 = 0.4.

3/8 (0.750) : 5 étapes de réduction et taille max 24 est suffisant !

4/11 (=0.363636364) : 6 étapes de réduction tailles [30, 26, 24, 24, 24] est suffisant !

17/48 (=0.354166667) : 6 étapes de réduction tailles [30, 26, 24, 24, 24] est suffisant !

1/3 : suffisant en 6 étapes de réductions avec les tailles [28; 26; 26; 26; 26] !!!
*)



