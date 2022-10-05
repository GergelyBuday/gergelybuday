---
layout: post
title:  "The HOL4 Syntax"
date:   2022-09-27 
categories: hol4
permalink: the-hol4-syntax
---

# Introduction

It's just syntax, said once a trained mathematician, and this has a grain of truth. Different higher-order theorem provers
do not differ too much in their definitional mechanisms, only in concrete syntax. Still, if you want to master them,
syntax is essential.

Here I would like to gather the most important surface syntax of the HOL4 theorem prover. 

# A Script file

HOL4 proof scripts are stored in XXXXScript.sml files. This file shows the basic Syntax:
```
open HolKernel bossLib

val _ = new_theory "trivial"

Theorem reflexivity:
  x = x
Proof
  simp []
QED

val _ = export_theory();
```
With open we can refer to existing HOL4 developments. For an extensive documentation of libraries, see 
the [HOL Reference Page](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/HOLindex.html). 

There are two main modes of using HOL4, the interactive mode that is helped with the hol-vim, emacs hol mode or the Visual Studio Code extension, and the batch mode, that is, running your script files through Holmake. In the interactive mode
you should load these libraries by hand, in batch mode it is done automatically. Interactively the keyword is "load", but
the user interfaces derive the component list from the "open" declaration. The interactive mode is a read-eval-print-loop
of the underlying SML compiler. The user interfaces are using this interactive loop.

"new\_theory" defines the name of the theory and starts the session. The file name's prefix should coincide with the string given here, otherwise you get an error message. So here my file is trivialScript.sml .

At the end of the file there is "export\_theory", which closes the session started with "new\_theory". Running Holmake will create a file that can be used from other script files, the same way as we imported system libraries with "open".

Between these there is a theorem and its proof in a Theorem-Proof-QED block. These keywords should start at the beginning of the line. We should give a name to the theorem, afterwards we can refer to it by this name. After theorem we can give the goal we would like to prove, after Proof there is the tactic that is meant to 
prove the goal.

# Definitions

The basic definitions of HOL4 are datatypes, functions, inductive relations, records (ADD LIST HERE).

A datatype is an algebraic type, familiar from functional languages. For a binary tree, we can write
```
Datatype `bintree = Leaf | Node bintree 'a bintree`
```
in HOL4 which is the equivalent of 
```
datatype 'a bintree = Leaf | Node of 'a bintree * 'a * 'a bintree
```
in Standard ML. As we can see, the HOL4 definition is more terse. Be aware of the use of backticks for the Datatype definition in HOL4. An alternative HOL4 syntax is
```
Datatype: btree = LEAF | NODE btree 'a btree
End
```
As before, the Datatype and End keywords should start their lines.

Defining a recursive function has this syntax:
```
Definition fibonacci_def:
  (fib 0 = 0) ∧
  (fib 1 = 1) ∧
  (fib n = fib (n-2) + fib (n-1))
End
```
As usual, the order of patterns matter, the first has precedence over the others, and so on. Also usual is the position of Definition and End at the start of the line.

For conjunction, we see the Unicode mathematical symbol. In hol-vim, these symbols can be entered
through digraphs. See the character combinations for them in 
[holabs.vim](https://github.com/HOL-Theorem-Prover/HOL/blob/develop/tools/vim/holabs.vim) in HOL4's github repository. The file starts with the part defining coding for the conjunction symbol:
```
iab <buffer> /\ ∧
"dig AN
```
In vim, we need to use CTRL-K and AN, as suggested in this snippet. See a full list of mathematical Unicode characters in hol-vim and their corresponding digraphs:
```
∧ AN conjunction
∨ OR disjunction
¬ NO -, negation
⇒ => implication
≤ =< less or equal
≥ >= greater or equal
⇔ == bi-implication, if and only if
≠ != not equal
∀ FA universal quantor, for all
∃ TE existential quantor, exists
λ l* the lambda operator
∈ (- element of
+ (+ not an element, this did not work,
     use ^Vu2209 instead for ∉, HOL4 will understand it
∩ (U meet of sets
∪ U) union of sets
⊆ (_ subset (might be equal)
⊂ (C proper subset (cannot be equal)
```
For defining inductive relations the syntax is:
```
Inductive Even:
  even 0 ∧
  ∀n. even n ⇒ even (n+2)
End
```

# Under the hood: parsing

In functional programming, interesting data structures are built using the constructors of data types. But, of course, it would be cumbersome to write
```
APP (APP (APP (IDENT "COND", IDENT "P"), IDENT "Q"), IDENT "R")
```
instead of 
```
if P then Q else R
```
So HOL4 has a parser that translates the surface syntax into primitive constructors.

# Lexing
