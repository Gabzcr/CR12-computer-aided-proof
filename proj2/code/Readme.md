## Getting Started #

To compile, simply type "make". The file produced is named "pgm".
Launch the demo with command **./pgm**.

For a demo that was not pre-computed, but is still fast, use the following commands (step 1 will erase pre-computation):
1) **`rm tree_files_2_5/\*`**
2) **`./pgm 2 5 5 20 20 20 20 20`**

When arguments are specified, here is how it works :
**`./pgm p q reduc size2 [other_sizes ...]`**  computes the forbidden factors in at most **reduc** steps of reduction, when trying to prove a bound alpha = **p/q**. The maximal sizes of forbidden factors are specified from **size2** on, one per number of reduction steps (we might want to compute shorter factors for a higher number of reduction steps to win time.)
For example, we can replace 2) above by **`./pgm 2 5 5 26 18 18 18 18`** to get same result. Here we look for factors forbidden for a bound 2/5, with at most 5 steps of reduction, such that the maximal size for only 2 steps of reduction is 26, and then the maximal size is 18 for at least 3 steps of reduction.
Note that starting with a size 20, then moving to sizes 18 is not enough.

Don't forget to use "make clean" between each make if you modified the code,
or pgm won't change.


## General Outline #

The program is split in two files. File *reduction.ml* contains all useful functions and the biggest part of the work. File *tests.ml* contains the printer functions, and uses the functions from *reduction.ml* to find sets of forbidden factors according to a given bound alpha. It also serves as a demo since lauching the program will execute its code.

### Main Idea #

Main function is **`wrong_factors`** from lines 444 to 628. It progressively fills in a table F ("forbidden") of dimension 2 such that F[i,j] contains the words from which we can retrieve at least i letters in at most j steps. For more explicit notations, we write F[reduc, steps].

This table is filled by dynamic programming (prog dyn). For each case, we make a backtrack over the words to find those satisfying the condition (function **`find_factors`** lines 501 to 547). At every tested word, we first check that there is no big square - otherwise we conclude in one step - then we try to reduce every possible square and see if we end up in a previous case of the table (computed recursively). This is checked by function **`is_forbidden`** from lines 576 to 606.

**How to conclude :** According to instructions, I will not re-explain here the full theory behind the method as I did for previous project (i.e the non-generation of infinite words dodging all "forbidden words" implying the bound).
The forbidden factors are those contained in all cases of the form **F[i,j]** where **i >= q/p.j**, since from them we can make a reduction chain that will remove enough letters. Note that cases F[i,j] are included in cases F[i',j] when i' is smaller that i (if we can remove at least i' > i letters, we can remove at least i letters too.)
So the set of forbidden factors is the union of factors in the cases **F[ceil(q/p.j), j]**. This is what **`find_factors`** returns.

Then we can test that there are no infinite word that doe not contain any of this factor by trying to generate a word of given size dodging them all. If there are no such word, then the given bound alpha = p/q is proven.
This is done by function **`generate`** from lines 402 to 420. Lines 0 to 400 contains useful functions called by these two functions presented here. These were already mostly explained in previous project.

A lot of work on optimisation was made for this project. Here is an overview of the ones that worked and were kept in the project.

## Optimisations #

#### Prefix/Suffix tree of factors #

How this structure works has already been explained in project 1. Storing factors in tree is both a huge gain of space and time. Here since the mirrors of forbidden words are also forbidden words, trees are both prefix and suffix trees.

We are only considering factors of minimal size for the tree. That is, if 001001 is in the tree then 001001001 cannot be in the tree since it already has a factor in the tree. This allows to cut a lot of the branches in the backtrack to speed it up.

#### Diverse shortcuts #

* **Complement of words :** When we test a word, we can also conclude for its reverse, its complement (0s instead of 1s and vice-versa), and the mirror of its complement. Thus, we only need to test words that begin with a 0 (the other are complements of words beginning with a 0), which divides the search space by 2. Line 508.

* **Reverse of words :** Also we don't need to test a word if we already tested its reverse. Thus only test words that are smaller lexicographically than their reverse. This again divides the search space by 2. Line 532

* **Reducing size in recursive calls :** When we are recursively calling our factor finding function, we need it on smaller factors. Since we reduced a square, we removed at least one letter so we need only check if the reduced word is in the table with a maximal size decreased by 1. This allows to greatly cut the search space (and time spent) on recursive call. The more we call recursively, the faster it gets to compute the needed tree. Line 596.

* **Adding a first inclusion :** Finally, a very small optimisation is the following. Instead of computing the factors from which we can remove at least i letters in j steps in case F[i,j], compute the factors from which there exists some k with 0 <= k <= max(j-1, i.q/p) and we can remove at least i-ceil(q/p).k letters in at most j-k steps. The idea is simply that this will add factors that are indeed forbidden at the end, and give a starting tree of forbidden factors from case F[i-ceil(q/p), j-1] that we then don't need to test. In practice, this optimisation makes almost no difference so we can just comment it. Lines 492-494.

#### Using files to store results #

This is the most important optimisation of all ! A lot of the computations for one of the cases F[i,j] can be re-used to compute other cases or deduce information for them. So whenever the program is done computing a case, it will store the result in a file for later use. Also computations can be reused from one run of the program to another. This is why the demo is so fast (everything has already been computed).
Files contain every word in the corresponding tree, one per line separated by "\n", written as a string of "0" or "1".
The name of the file representing  case F[i,j] is "**tree_files_p_q/f_i_j_size.txt**" where :
* p/q = alpha is the bound we try to achieve. dir_name = "tree_files_p_q/".
* i= reduc is the number of letters to remove
* j = steps is the number of reduction steps allowed to remove letters
* size is the maximal size of tested factors

**Now what does this allow me to do ?**

1) If the case F[i,j] has been computed in a previous run of the program, take it instead of computing it. The result can be simply re-used as long as the maximal size of factors in the file is bigger than the maximal size we are currently asking for. Lines 466 to 472.

2) If a file exists but contains smaller factors (say of size at most n while we are asking for bigger factors), then still put them all in the tree of forbidden factors that we are building, and in the backtrack only test for words of size > n. Lines 482 to 488 and 532.

3) If a case in the table below the current one has already been filled, put it in the tree of forbidden factors since it is included (more letters removed in the same number of steps). This can spare a few tests. Line 477.

4) More interestingly, if a case in the table above the current one has already been filled, then we can make a faster backtrack. We know our current tree is "included" in this one. Unfortunately, we cannot just test every factor from above to build our tree. We could have a factor above from which we could remove 8 letters but we cannot remove 9 letters. In that case, we need to test every word that contains this factor to try and reach for more letters.
However the tree from above can still be useful in the way that if we couldn't even remove 8 letters from a word, we won't be able to remove 9 letters. Thus, we can "wait" to reach a factor in the above tree before beginning to test for our tree. So long as we are a prefix of a factor in above tree, don't bother testing. Once we have reached it, test and backtrack further until we find a new forbidden word or the maximal size of factors. Implemented lines 510 to 530.
--> This is a big speedup.

#### Extending factors when a few letters are missing #

This is also an important optimisation, and it is not even complex.
The idea is that when we need to remove less than 2 letters (per step of reduction), then we are sure to be able to reach this by extending our word, no matter how we extend it. Indeed, every word of size at least 18 has a square of size at least 2. This also allows to search for factor of smaller size and with less reduction steps than would be necessary otherwise, making a huge gain of time (and a small gain of space). See implementation in lines 589-590.
