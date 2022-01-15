### Getting Started #

To compile, simply type "make". The file produced is named "pgm".
Launch the demo with command ./pgm.

Don't forget to use "make clean" between each make if you modified the code,
or pgm won't change.



### General Outline #

The program is split in two files. File *word.ml* contains all useful functions and the biggest part of the work. File *tests.ml* contains the printer functions, and uses the functions from *word.ml* to find interesting values and words such as the (d,alpha) couple, the morphisms, checking conditions, etc. It also serves as a demo since lauching the program will execute its code.

File word.ml :

The code is divided in parts, that are documented directly in the file. Line numbers are indicated on the left.
* Lines 2-45 : **Rational numbers.**  Provides a type for rational numbers in Ocaml and a small library for manipulating them.
* Lines 46-122 : **Words.** Provides a few functions for manipulating words : taking a prefix, generating Thue Morse sequences and applying a morphism.
* Lines 123-217 : **Binary tree.**  Provides a type for unlabeled binary trees representing binary words and functions to manipulate them (adding a word in a tree, etc.).
* Lines 218-303 : **Tests for directedness and freeness.**  Provides functions for checking that words are d-directed and alpha(+)$-free, both on the fly when adding a letter to a word satisfying the property and in general.
* Lines 304-356 : **Tests for morphisms images.** Provides a test to check that every concatenation of three words (images of a morphism from ternary alphabet) is alpha(+)-free, and that such a morphism is synchronizing.
* Lines 357-546 : **Backtrackings.** This is the main part of the code. Generates d-directed alpha(+)-free words of given sizes, and morphisms satisfying all the conditions listed in the theorem of the article.
* Lines 547-584 : **Checking lemma hypothesis.** Provides a function computing the "max" bound from the theorem and a function checking that images of 7/4+-free ternary word of this maximal size are alpha+-free by enumerating them.
Lines 585-632 : **Dichotomy.** Provides the dichotomy used to find tight alpha for each d value.

Note : d-directedness was implemented first by manipulating trees and words. As a consequence, words were first implemented as lists. Later on, tests of alpha-freeness were way easier to do with arrays than with a list since we want to access letters at given positions in the word. Thus, some words are represented by a list and some others by an array, and conversions are often required.

File tests.ml is self-explanatory, especially when running the demo.

### The most important functions of the code : #

* **d\_directed\_alpha\_free** d alpha l plus : This is the function that generates by backtracking a d-directed and free word of size l. If plus is set to true, the generated word is alpha+-free, else the generated word is alpha-free. Returned word is given in an array.
* **homomorphism\_alpha** d q alpha plus : This is the function that generates by backtracking the three images of a q-uniform morphism from a ternary alphabet to a binary alphabet, satisfying that concatenations of these images are d-directed and alpha-free, and some other conditions. See article for more details on the conditions satisfied by the morphism.

Others :
* **compute\_bound** alpha beta q : Finds the maximum size of ternary alpha+-free words for which we need to test that the image of a q-uniform morphism are beta+-free (cf Theorem from the article). So that **images\_are\_free** phi bound alpha beta : enumerates these words by backtracking and run these tests on images by morphism phi.
