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


(*
let size = 24 in
let nb_reduc = 2 in
Printf.printf "Creating forbidden factors of size at most %d for at most %d reduction steps.\n" size nb_reduc;
let forbid = wrong_factors nb_reduc size in
(*print_tree_as_factors forbid;
print_list_of_list (tree_to_list_of_factors forbid);*)
Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
Printf.printf "Trying to generate a word of size 10000 avoiding all these factors :%!\n";
print_array (generate forbid 10000 (1,3));
Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.\n"
*)


let size = int_of_string (Sys.argv.(1)) in
let nb_reduc = int_of_string (Sys.argv.(2)) in
let alpha = (int_of_string (Sys.argv.(3)), int_of_string (Sys.argv.(4)))in
Printf.printf "Creating forbidden factors of size at most %d for at most %d reduction steps.\n" size nb_reduc;
let forbid = wrong_factors nb_reduc size alpha in
let forbid2 = tree_add forbid [|0;0;1;0;0|] 4 true in
let forbid3 = tree_add forbid2 [| 1;1;0;1;1|] 4 true in 
let liste_finale = (tree_to_list_of_factors forbid) in
(*print_tree_as_factors forbid;
print_list_of_list liste_finale;*)
Printf.printf "We forbid %d factors with this method.\n" (nb_of_factors_in_tree forbid);
Printf.printf "Trying to generate a word of size 1000 avoiding all these factors :%!\n";
print_array (generate forbid3 1000 alpha);
Printf.printf "Empty array means there are no word of required size dodging all forbidden factors with no big square.%!\n";;

Printf.printf "Test sur mot particulier :%b\n" (is_forbidden_base [|1;1;1;1;1;0;1;1;0;0;1;1;1;1;1;0;0|] 16 7);;



(*
let res = ref true in
let word = ref [] in
let rec check_list l = match l with
	| [] -> Printf.printf "end of check\n"
	| h::t -> try
				let (i,j) = reduce_ratio (Array.of_list h) (List.length h - 1) (3,1) 0 0 in
				Printf.printf "Not found : (%d,%d)\n" i j;
				res := false;
				word := h;
			with Found(i,j) -> (Printf.printf "Found : (%d,%d)\n" i j; check_list t)
in
(*
try
	let (i,j) = (reduce_ratio [| 0;0;1;0;1 |] 4 (3,1) 0 0) in
	Printf.printf "Not found : (%d,%d)\n" i j;
with Found(i,j) -> Printf.printf "Found : (%d,%d)" i j;*)
check_list liste_finale;
print_string "Fini\n";
if not(!res) then
begin
	Printf.printf "FAUX :\n";
	print_list (!word)
end;;*)

(*
Creating forbidden factors of size at most 24 for at most 7 reduction steps. (2/5)
We forbid 91346 factors with this method.
Trying to generate a word of size 1000 avoiding all these factors :
[|0;0;0;0;0;1;0;1;0;0;0;0;1;1;0;0;1;0;1;0;1;1;0;0;0;0;0;1;1;1;0;1;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;1;0;1;0;1;0;0;0;0;1;0;1;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;0;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;1;1;0;0;0;0;0;1;0;1;1;1;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;0;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;0;0;0;1;1;0;0;1;0;1;0;1;1;0;0;0;0;0;1;1;1;0;1;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;1;0;1;0;1;0;0;0;0;1;0;1;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;0;0;0;1;0;1;1;1;0;0;0;0;1;1;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;0;1;1;1;0;0;0;0;1;0;1;0;0;0;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;0;0;1;1;0;0;0;0;0;1;0;1;1;1;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;0;1;0;1;0;0;0;1;1;0;1;0;0;1;1;0;0;0;0|]
*)


let word = [|0;0;0;0;0;1;0;1;0;0;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;0;0;0;0;0;1;1;1;1|]
in print_list_as_word (Array.to_list word);
(*
for i = 0 to 0(*(Array.length word - 25)*) do
	try
		let (r,s) = reduce_ratio (Array.sub word i 24) 23 (1,3) 0 0 in
		Printf.printf "Factor beginning at pos %i is not forbidden, best ratio is (%d,%d)\n" i r s
	with Found(i0,j) -> (Printf.printf "Found : (%d,%d)\nFor word : \n" i0 j;
		print_array (Array.sub word i 15))
done;;*)


(*------------------RESULTAT------------------------*)
(*
Factors of size 21 and maximum 5 reduction steps are enough to prove bound 2/5 = 0.4.
But not 1/3.

Factors of size 24 and maximum 7 reduction steps gives :
[|0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;1;1;1;1;1;0;0;1;0;1;0;0;0;0;0;1;0;1;1;1;0;0;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;1;0;0;1;1;0;1;0;1;0;0;0;0;1;0;1;1;1;1;1;0;0;0;1;1;0;0;1;0;1;0;0;0;0;0;1;0;1;1;1;1;1;0;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1;1;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;1;1;1;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;0;1;0;1;1;1;1;1;0;1;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;1;1;1;1;1;0;0;1;0;1;0;0;0;0;0;1;0;1;1;1;0;0;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;1;0;0;1;1;0;1;0;1;0;0;0;0;1;0;1;1;1;1;1;0;0;0;1;1;0;0;1;0;1;0;0;0;0;0;1;0;1;1;1;1;1;0;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1;1;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;1;1;1;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;0;1;0;1;1;1;1;1;0;1;0;0;0;1;1;0;0;1;0;1;0;1;1;0;0;0;0;0;1;1;1;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;0;0;0;1;0;1;1;1;1;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;0;1;0;1;1;1;1;1;0;1;0;0;0;1;1;0;1;0;1;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;1;0;0;0;1;1;0;0;1;0;1;0;0;0;0;0;1;0;1;1;1;1;1;0;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;1;0;1;0;1;0;0;0;0;0;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;1;0;1;0;1;0;0;0;1;1;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1;1;0;0;1;0;1;0;0;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;0;1;1;1;1;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0|]
--> 28734 forbidden factors (not including biq squares)
*)


(*
0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1
0;0;0;0;0;1;0;0;1;1;0;0;0;0;0;1;1        (-2)
0;0;0;0;0;1;1;0;0;0;0;0;1;1       (-3)
0;0;0;0;0;1;1        (-7) --> ok

0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;1;1

0;0;0;0;0;1;0;1;0;0;1;1;0;0;0;0;0;1;1
1;1;1;1;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0
1;1;1;1;1;0;1;1;0;0;1;1;1;1;1;0;0 (-2)
1;1;1;1;1;0;0;1;1;1;1;1;0;0 (-3)
)1;1;1;1;1;0;0 (-7)
*)

(*Résultat 24 7 1 3
We forbid 103746 factors with this method.
Trying to generate a word of size 1000 avoiding all these factors :
[|0;0;0;0;0;1;0;1;0;0;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;1;0;1;0;0;0;0;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;1;1;0;0;0;0;0;1;0;1;0;1;0;0;1;1;1;1;1;0;0;0;0;0;1;1;0;1;0;1;0;1;1;0;0;1;1;1;0;0;0;0;0;1;1;1;1|]

2/5 : 20 5 2 5 est suffisant
3/8 (0.750) : 21 5 3 8 pas concluant. 24 6 3 8 est suffisant ! (180678 facteurs interdits).
5/13 (environ 0.385) : 21 6 5 13 pas concluant (on peut construire un mot infini)
9/23 (environ 0.391) : 21 6 9 23 pas concluant (88008 facteurs interdits). 24 6 9 23 
19 / 48 (environ 0.395833333) : 21 5 19 48 pas concluant (49238 facteurs interdits).
*)



