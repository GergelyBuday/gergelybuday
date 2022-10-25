---
layout: post
title:  "The HOL4 Syntax"
date:   2022-09-27 
categories: hol4
permalink: the-hol4-syntax
---

## Introduction

It's just syntax, said once a trained mathematician, and this has a grain of truth. Different higher-order theorem provers
do not differ too much in their definitional mechanisms, only in concrete syntax. Still, if you want to master them,
syntax is essential.

Here I would like to gather the most important surface syntax of the HOL4 theorem prover. 

## A Script file

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
With open we can refer to existing HOL4 libraries. For an extensive documentation of libraries, see 
the [HOL Reference Page](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/HOLindex.html). 

There are two main modes of using HOL4, the interactive mode that is helped with the hol-vim, emacs hol mode or the Visual Studio Code extension, and the batch mode, that is, running your script files through Holmake. In the interactive mode
you should load these libraries by hand, in batch mode it is done automatically. Interactively the keyword is "load", but
the user interfaces derive the component list from the "open" declaration. The interactive mode is a read-eval-print-loop
of the underlying SML compiler. The user interfaces are using this interactive loop.

The command "new\_theory" defines the name of the theory and starts the session. The file name's prefix should coincide with the string given here, otherwise you get an error message. So here my file is trivialScript.sml .

At the end of the file there is "export\_theory", which closes the session started with "new\_theory". Running Holmake will create a file that can be used from other script files, the same way as we imported system libraries with "open".

Between these there is a theorem and its proof in a Theorem-Proof-QED block. These keywords should start at the beginning of the line. We should give a name to the theorem, afterwards we can refer to it by this name. After theorem we can give the goal we would like to prove, after Proof there is the tactic that is meant to 
prove the goal.

## Definitions

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

For defining inductive relations the syntax is:
```
Inductive Even:
  even 0 ∧
  ∀n. even n ⇒ even (n+2)
End
```

## Types

<!-- type grammar with explanation -->

HOL4 gives us its type grammar with the command type\_grammar:
```
> type_grammar();
val it =
   Rules:
     (50)   TY  ::=  TY -> TY [fun] (R-associative)
     (60)   TY  ::=  TY + TY [sum] (R-associative)
     (70)   TY  ::=  TY # TY [prod] (R-associative)
            TY  ::=  bool | (TY, TY) fun | ind | TY itself | TY list | num |
                     one | TY option | (TY, TY) prod | TY recspace | TY set |
                     (TY, TY) sum | unit
            TY  ::=  TY[TY] (array type)
   Type abbreviations:
     bool             = min$bool
     (α, β) fun       = (α, β) min$fun
     ind              = min$ind
     α itself         = α bool$itself
     α list           = α list$list
     num              = num$num
     one              = one$one                [not printed]
     α option         = α option$option
     (α, β) prod      = (α, β) pair$prod
     α recspace       = α ind_type$recspace
     α set            = (α, min$bool) min$fun  [not printed]
     (α, β) sum       = (α, β) sum$sum
     unit             = one$one               : type_grammar.grammar

```
Here I explain only non-standard notation. At the beginning we see the notation for function, sum and record types, with record type being the somewhat unusual hash mark, not
the standard star. All these are right-associative, A op B op C means A op (B op C). The ind type is the one for individuals, as we know it in formal logic. For any type, α itself is a one-element type whose element represents the type. Its role is technical in building more complex types like the fixed width word type. The type num is the type of natural numbers. The type one is the same as the unit type with the only element (). Type α recspace is again a technical type used in the type definition package, holding finitely branching recursive types built from subsets of α. For an expert description see 
[an old mail of John Harrison](https://hol-info.narkive.com/ozgDo69L/recspace).
## Lexing 

## Parsing

In functional programming, interesting data structures are built using the constructors of data types. But, of course, it would be cumbersome to write
```
APP (APP (APP (IDENT "COND", IDENT "P"), IDENT "Q"), IDENT "R")
```
instead of 
```
if P then Q else R
```
So HOL4 has a parser that translates the surface syntax into primitive constructors. Similarly to type\_grammar, function term\_grammar gives us the current state of the grammar used in parsing. I inject explanations to the output of the command to make it understandable.
```
> term_grammar();
val it =
   (0)    TM  ::= "OLEAST" <..binders..> "." TM
                | "LEAST" <..binders..> "." TM | "some" <..binders..> "." TM
                | "∃!" <..binders..> "." TM [?!] | "?!" <..binders..> "." TM
                | "∃" <..binders..> "." TM [?] | "?" <..binders..> "." TM
                | "∀" <..binders..> "." TM [!] | "!" <..binders..> "." TM
                | "@" <..binders..> "." TM | "λ" <..binders..> "." TM
                | "\" <..binders..> "." TM
```
First, binders. If c is a binder, c x. t translates to $c \\x.t, that is, the standard syntax version of
the binder applied to the lambda abstraction  λx.t . Also, c x1 x2 .. xN . t translates to c x1. c x2. .. c xN . t .

The LEAST binder works on functions defined for natural numbers, giving back the least number that satisfies its argument predicate: ∀P. $LEAST P = WHILE ($¬ ◦ P) SUC 0 . The while loop starts from 0 and goes until a successor satisfies predicate P. The binder OLEAST is an option valued binder that gives SOME n when LEAST would define a concrete value and NONE otherwise: ∀P. $OLEAST P = if ∃n. P n then SOME (LEAST n. P n) else NONE .

To explain "some", take binder @, which is a higher order version of Hilbert's choice operator ε, an element that satisfies a predicate P, given there is such an element: ∃x.P x ⇒ P(@x.P x) . The binder some (not to mistake for the SOME constructor of the option type) is ∀P. $some P = if ∃x. P x then SOME (@x. P x) else NONE, it tells us whether the choice operator would return a real value satisfying the relation.

Then comes the uniquely exists quantor ∃! and its ASCII counterpart ?!, the exists quantor ∃ and its ASCII version ?, the universal quantor ∀ and ASCII !, the lambda operator λ and its ASCII equivalent \\ .
```
   (1)    TM  ::= "case" TM "of" TM "|" TM "|" TM
                    [case magic$default - %case%]
                | "case" TM "of" "|" TM  [case magic$default - %case%]
                | "case" TM "of" TM "|" TM  [case magic$default - %case%]
                | "case" TM "of" TM  [case magic$default - %case%]
```
The case construction. Here is an example that explains itself:
```
case n of
  0 => "none"
| 1 => "one"
| 2 => "two"
| _ => "many"
```
Writing a vertical bar in front of the first case 0 is also valid syntax.
```
   (4)    TM  ::= TM "::" TM (restricted quantification operator)
   (5)    TM  ::= TM TM  (binder argument concatenation)
   (8)    TM  ::= "let" LTM< _ letnil, _ letcons,;> "in" TM  [ _ let]
   (9)    TM  ::= TM "and" TM  [ _ and]   (L-associative)
   (12)   TM  ::= TM "=>" TM  [case magic$default - %arrow%]
                    (non-associative)
```
Restricted quantification is giving a bounding set for the values of the bound variable: (\\ x :: P. M) = M[y/x] only if y ∈ P. Binder argument concatenation is the case I described above: we can write only one binder with a list of bound variables. The let construct is let v = M in N. The left-associative "and" construct is the one we can use in a let expression: let v = M and u = P in N. The arrow => is the mapping of a value to a pattern in a case construction, see the previous HOL4 example.
```
   (50)   TM  ::= TM "," TM     (R-associative)
   (70)   TM  ::= "if" TM "then" TM "else" TM  [COND]
   (80)   TM  ::= TM ":-" TM     (non-associative)
   (100)  TM  ::= TM "↦" TM  [  combinpp.leftarrow]
                | TM "|->" TM  [  combinpp.leftarrow] | TM "⇎" TM  [<=/=>]
                | TM "<=/=>" TM   | TM "⇔" TM  [<=>] | TM "<=>" TM
                    (non-associative)
   (200)  TM  ::= TM "⇒" TM  [==>] | TM "==>" TM     (R-associative)
```
The right-associative comma is the pair constructor. There's no need for an explanation of the if-then-else construct that translates to the COND internal primitive, as seen above. An input syntax for the turnstile logical symbol is :- . It is used only in low-level definitions. The maplet symbol ↦ and its ASCII equivalent |-> is the finite map type operator. For logical equivalence and non-equivalence, there is ⇔ and ⇎, and their ASCII counterpart <=> and <=/=> . For logical implication there is
⇒ and the ASCII ==> .
```
   (300)  TM  ::= TM "∨" TM  [\/] | TM "\/" TM     (R-associative)
   (310)  TM  ::= TM ":>" TM     (L-associative)
   (320)  TM  ::= TM "=+" TM  [UPDATE]   (non-associative)
   (400)  TM  ::= TM "∧" TM  [/\] | TM "/\" TM     (R-associative)
   (425)  TM  ::= TM "refines" TM   | TM "partitions" TM
                | TM "equiv_on" TM   | TM "∉" TM  [NOTIN] | TM "NOTIN" TM
                | TM "∈" TM  [IN] | TM "IN" TM
                    (non-associative)
```
There is ∨ for logical or and its ASCII equivalent \/ . The :> operator is reverse function application: x :> f is f x. And it lets us write x :> g :> f for f(g(x)) . The =+ symbol is function update: (a =+ b) f updates f with value b at argument a . For logical and there is ∧ and its ASCII counterpart /\ . For two set of sets, A refines B if for every element set of A there is an element of B so that the former is a subset of the latter: for a ∈ A there is b ∈ B so that a ⊆ b . The infix equiv_on operator tells that a relation R is an equivalence relation on the underlying set S, that is, R is reflexive, symmetric and transitive. The expression X partitions Y holds when X is a set of sets, the partition of Y according to some equivalence relation R. For set membership and non-membership there is ∈ and ∉ and their ASCII notation IN and NOTIN .

```
   (450)  TM  ::= TM "≼" TM  [<<=] | TM "<<=" TM   | TM "PERMUTES" TM
                | TM "HAS_SIZE" TM   | TM "⊂" TM  [PSUBSET]
                | TM "PSUBSET" TM   | TM "⊆" TM  [SUBSET] | TM "SUBSET" TM
                | TM "≥" TM  [>=] | TM ">=" TM   | TM "≤" TM  [<=]
                | TM "<=" TM   | TM ">" TM   | TM "<" TM
                | TM "⊆ᵣ" TM  [RSUBSET] | TM "RSUBSET" TM   | TM "≠" TM
                | TM "<>" TM   | TM "=" TM
                    (non-associative)
```
The unicode symbol ≼ and its ASCII version &lt;&lt;= is for the list prefix partial order isPREFIX . 
The infix operator PERMUTES tells that PERMUTES f dom if f is a bijection on dom. 
For HAS\_SIZE, A HAS\_SIZE n if A is a finite set and has n elements. The notation for subset and
proper subset is SUBSET and PSUBSET, and the usual symbols. For usual ordering relations HOL4 has
the usual symbols. The operator RSUBSET is a subset relation for relations. Equality and non-equality is again the usual.

```
   (460)  TM  ::= TM "$" TM  [_ fnapp] | TM "with" TM  [record update]
                | TM ":=" TM  [record field update]
                | TM "updated_by" TM  [functional record update]
                    (R-associative)
```
The dollar symbol is a low-precedence function application symbol: FACT $ SUC $ 2 + 3 = FACT(SUC(2+3)), spares a few parentheses.
This is a Haskell notation. Other than solo dollar, dollar immediately followed by a possibly symbolic identifier returns a normal function that can be
used as a function argument: ASCII tilde, ~ is negation, $~ is a usable name for a function argument. When the identifier is infix, dollar removes its infix status and the combined identifier can be used as a prefix function name. 

The keyword with and symbolic identifier := can be used in a record field update: rec with fieldname := new\_value . Using
updated\_by allows us to apply a function to a record field: bob with employed updated\_by $~ , this inverts the boolean field employed. And, it is right-associative.
```
   (480)  TM  ::= TM "⧺" TM  [++] | TM "++" TM   | TM "+++" TM
                    (L-associative)
   (490)  TM  ::= TM "::" TM  [CONS] | TM "INSERT" TM
                | TM "###" TM  [PAIR_REL] | TM "LEX" TM   | TM "##" TM
                    (R-associative)
```
The ASCII double plus, ++ operator and its Unicode variant ⧺ is list append. The triple plus +++ is an operator on relations: its type is
:(α -> β -> bool) -> (γ -> δ -> bool) -> α + γ -> β + δ -> bool, so it creates a componentwise sum type for the two relations.

The double colon :: is the cons operation as suggested: extending a list with an element on the left. The keyword INSERT is set insertion:
1 INSERT {1;3} = {1;3} . The triple hash mark ### operates on two relations and gives back a relation that is of componentwise products of the
original relations' base types: :α # γ -> β # δ -> bool , from :α -> β -> bool and :γ -> δ -> bool . 
```
   (500)  TM  ::= TM "⊔" TM  [disjUNION] | TM "<+>" TM  [disjUNION]
                | TM "DELETE" TM   | TM "DIFF" TM   | TM "∪" TM  [UNION]
                | TM "UNION" TM   | TM "<*>" TM  [APPLICATIVE_FAPPLY]
                | TM "−" TM  [-] | TM "-" TM   | TM "+" TM
                | TM "∪ᵣ" TM  [RUNION] | TM "RUNION" TM
                    (L-associative)
   (600)  TM  ::= TM "∩" TM  [INTER] | TM "INTER" TM   | TM "\\" TM
                | TM "DIV" TM   | TM "*" TM   | TM "∩ᵣ" TM  [RINTER]
                | TM "RINTER" TM
                    (L-associative)
   (601)  TM  ::= TM "×" TM  [CROSS] | TM "CROSS" TM   | TM "⊗" TM  [*,]
                | TM "*," TM
                    (R-associative)
```
The <+> and its Unicode counterpart ⊔ is disjoint union for relations: for types :α -> bool and :β -> bool it gets :α + β -> bool. 
The infix operator DELETE deletes an element from a set. The next one, DIFF is set difference. The meaning of UNION and its Unicode variant
∪ is obviously set union. The infix operator <\*>, nicknamed APPLICATIVE\_FAPPLY applies all functions in a function list to a list of arguments and concatenates the resulting lists: [(λx. x + 2); (λx. x + 4)] <*> [1; 2; 3] = [3; 4; 5; 5; 6; 7] . 

The Unicode minus sign seems to be just an alias to standard ASCII minus sign - . The ASCII plus + is addition for natural numbers, of type num.
The infix operator RUNION or its Unicode equivalent ∪ᵣ lifts set union operation to relations, and so does RINTER and ∩ᵣ for intersection. 
The infix INTER and its Unicode counterpart ∩ is obviously set intersection. The infix \\\\ is an operator on finite maps, it removes the right argument from the domain of the finite map on the left.

The infix DIV is obviously natural number division, and ASCII star is natural number multiplication. The infix CROSS and its Unicode notation × creates a cross product of two sets, on other words, a set of pairs: :α # β -> bool . Remember that hash mark # is for the product type. The infix ASCII *, operator on natural numbers and its Unicode variant ⊗ allows us to encode two natural numbers in one through triangular numbers. It is possible then to decode the first and second number from this encoded value.
```
   (650)  TM  ::= TM "%%" TM   | TM "MOD" TM     (L-associative)
   (700)  TM  ::= TM "**" TM   | TM "EXP" TM     (R-associative)
```
The symbolic identifier %% looks like a modulo operation before MOD but it is in fact a derived operation: CEILING_MOD m n = (n - m MOD n) MOD n .
MOD is the usual modulo operation. The standard EXP and its symbolic counterpart \*\* is natural number exponentiation. 
```
   (800)  TM  ::= TM "∘ᵣ" TM  [O] | TM "O" TM   | TM "∘" TM  [o]
                | TM "o" TM
                    (R-associative)
```
Capital O and its symbolic counterpart ∘ᵣ is relation compióosition, while small o and Unicode ∘ is function composition.
```
   (899)  TM  ::= TM ":" TY  (type annotation)
   (900)  TM  ::= "&" TM   | "-" TM  [numeric_negate] | "¬" TM   | "~" TM
   (2000) TM  ::= TM TM  (function application)   (L-associative)
```
With a weak precedence, colon : is for type annotation. 
The standard minus sign is numeric negation. The ASCII tilde ~ and its Unicode counterpart ¬ is for boolean negation.
Function application, writing terms consecutively with only whitespace has a low precedence to allow constructing arguments without parentheses.
```
   (2100) TM  ::= TM "³"   | TM "²"   | TM "ᵀ"  [relinv] | TM "^="  [EQC]
                | TM "꙳"  [RTC] | TM "^*"  [RTC] | TM "⁺"  [TC]
                | TM "^+"  [TC]
                | TM "⦇" LTM<  combinpp.nil,  combinpp.cons,;> "⦈"
                    [  combinpp.toplevelupd]
                | TM "(|" LTM<  combinpp.nil,  combinpp.cons,;> "|)"
                    [  combinpp.toplevelupd]
```
The superscripts ()³ and ()² are obviously cubic and quadratic powers. The superscript T, Unicode ()ᵀ is the inverse of a relation. 
The following are closures of a relation of type A x A , for it is meaningful if we can compose the relation with itself. Equality closure is ^=, 
reflexive transitive closure is ^* and Unicode ꙳, and transitive closure is ^+ or Unicode ()⁺ .

The delimiters (| and |) and their Unicode equivalent ⦇ and ⦈ are for function update: (\x.x) (| 2 |-> 3 |) creates a function that is the identity function on natural numbers, except that for argument 2 it gives back 3. And so does the Unicode notation (λx. x)⦇2 ↦ 3⦈ .
```
   (2200) TM  ::= "𝕌" TM   | "univ" TM
   (2500) TM  ::= TM "." TM  [record field selection]   (L-associative)
          TM  ::= "[" LTM<NIL,CONS,;> "]"  [ListForm<NIL,CONS>]
                | "{" LTM<EMPTY,INSERT,;> "}"  [ListForm<EMPTY,INSERT>]
                | "{" TM "|" TM "|" TM "}"  [gspec2 special]
                | "{" TM "|" TM "}"  [gspec special] | "(" ")"  [one]
                | "<|" LTM< _ record nil, _ record cons,;> "|>"
                    [ListForm< _ record nil, _ record cons>]
                | "(" TM ")"  [just parentheses, no term produced]
```
The identifier univ and Unicode 𝕌 is for the universal set of a type. Its definition is ⊢ 𝕌(:α) = (λx.T), in other words, any element of the type is an element of the universal set. The usual dot notation is for record
field selection, rec.fieldname . Square brackets with semicolons are for lists: type\_of ``[1;2;3]``; returns
“:num list”. Curly braces with semicolons are for concrete sets: type_of ``{1;2;3}``; returns “:num -> bool”. Sets are modelled with their characteristic function on their base type. Curly braces with vertical bars allow us
to write set comprehensions: ⊢ ∀s t. s DIFF t = {x | x ∈ s ∧ x ∉ t} . The usual hermite () is the only element of type one and the isomorphic type unit.


 Record specifications and values can be written with <| and semicolons and |> : for a specification let's have 
```
Datatype: person = <| employed : bool ; age : num ; name : string |>
End
```
 and for a value let's have 
```
<| age := 21; employed := F; name := "Layabout" |>
```
The following output does not convey new information about symbolic identifiers so I trimmed it:
```
   Known constants:
       _ fakeconst4.case,S10.case magic,7.default ! ## %% & () * ** *, + ++
     +++ , - /\ 0 :- :> < <<= <= <=/=> <=> <> = ==> > >= ? ?! @ ABS_DIFF
```
<!--
     ABS_num ABS_prod ABS_sum AC ALL_DISTINCT ALL_EL AND_EL APPEND
     APPLICATIVE_FAPPLY APPLY_REDUNDANT_ROWS_INFO ARB ASM_MARKER ASSOC Abbrev
     BIGINTER BIGUNION BIJ BIT1 BIT2 BOUNDED BUTFIRSTN BUTLAST BUTLASTN CARD
     CEILING_DIV CEILING_MOD CHOICE COMM COMPL COND CONS COUNTABLE COUNT_LIST
     COUNT_LIST_AUX CR CROSS CURRY Case Cong DATATYPE DELETE DFUNSET DIFF
     DISJOINT DIV DIV2 DIVMOD DROP EL ELL EMPTY EMPTY_REL EQC EVEN EVERY
     EVERY2 EVERYi EXISTS EXP EXT_POINT Exclude ExcludeFrag F FACT FAIL FCOMM
     FILTER FIND FINITE FIRSTN FLAT FOLDL FOLDL2 FOLDR FOLDRi FRAG FRONT FST
     FUNPOW FUNSET GENLIST GENLIST_AUX GSPEC GUESS_EXISTS GUESS_EXISTS_GAP
     GUESS_EXISTS_POINT GUESS_FORALL GUESS_FORALL_GAP GUESS_FORALL_POINT
     HAS_SIZE HD HOARE_SPEC I IDEM IMAGE IN INDEX_FIND INDEX_OF
     INDUCTIVE_INVARIANT INDUCTIVE_INVARIANT_ON INFINITE INJ INL INR INSERT
     INTER INVOL ISL ISR IS_EL IS_NONE IS_NUM_REP IS_PREFIX
     IS_REDUNDANT_ROWS_INFO IS_REMOVABLE_QUANT_FUN IS_SOME IS_SUBLIST
     IS_SUFFIX IS_SUM_REP ITSET Id IfCases K LAST LASTN LEAST LEFT_ID LEN
     LENGTH LET LEX LINV LINV_OPT LIST_APPLY LIST_BIND LIST_ELEM_COUNT
     LIST_GUARD LIST_IGNORE_BIND LIST_LIFT2 LIST_REL LIST_RELi LIST_TO_SET
     LLEX LRC LUPDATE LinearOrder MAP MAP2 MAP2i MAPi MAPi_ACC MAX MAX_SET
     MEM MIN MIN_SET MOD MODEQ MONOID NIL NONE NOTIN NRC NULL NUMERAL NUMFST
     NUMLEFT NUMRIGHT NUMSND O ODD OLEAST ONE_ONE ONTO OPTION_ALL
     OPTION_APPLY OPTION_BIND OPTION_CHOICE OPTION_GUARD OPTION_IGNORE_BIND
     OPTION_JOIN OPTION_MAP OPTION_MAP2 OPTION_MCOMP OPTREL OPT_MMAP OR_EL
     OUTL OUTR OWHILE Order PAD_LEFT PAD_RIGHT PAIR_REL PAIR_SET PERMUTES PI
     PMATCH PMATCH_EQUIV_ROWS PMATCH_EXPAND_PRED PMATCH_FLATTEN_FUN
     PMATCH_INCOMPLETE PMATCH_IS_EXHAUSTIVE PMATCH_ROW PMATCH_ROW_COND
     PMATCH_ROW_COND_EX PMATCH_ROW_COND_NOT_EX_OR_EQ PMATCH_ROW_LIFT
     PMATCH_ROW_REDUNDANT PMATCH_ROW_magic_0 PMATCH_ROW_magic_1
     PMATCH_ROW_magic_2 PMATCH_ROW_magic_3 PMATCH_ROW_magic_4 PMATCH_magic_1
     POW PRE PREFIX PREIMAGE PRIMES PRIM_REC PRIM_REC_FUN PROD_ALL PROD_IMAGE
     PROD_SET PSUBSET PreOrder RC RCOMPL RDOM RDOM_DELETE
     REDUNDANT_ROWS_INFOS_CONJ REDUNDANT_ROWS_INFOS_DISJ RELPOW REL_RESTRICT
     REMPTY REPLICATE REP_num REP_prod REP_sum REST RESTRICT RES_ABSTRACT
     RES_EXISTS RES_EXISTS_UNIQUE RES_FORALL RES_SELECT REV REVERSE RIGHT_ID
     RINTER RINV RPROD RRANGE RRESTRICT RSUBSET RTC RUNION RUNIV Req0 ReqD S
     SC SCANL SCANR SEG SET_TO_LIST SHORTLEX SIGMA SIMPLE_GUESS_EXISTS
     SIMPLE_GUESS_FORALL SIMP_REC SIMP_REC_REL SING SINGL SN SND SNOC SOME
     SOME_EL SPLITL SPLITP SPLITP_AUX SPLITR STRONGEST_REDUNDANT_ROWS_INFO
     STRONGEST_REDUNDANT_ROWS_INFO_AUX STRORD SUBSET SUC SUC_REP SUFFIX SUM
     SUM_ACC SUM_ALL SUM_FIN SUM_IMAGE SUM_MAP SUM_REL SUM_SET SURJ SWAP
     StrongLinearOrder StrongOrder T TAKE TC THE TL TL_T TYPE_DEFINITION
     UNCURRY UNION UNIQUE UNIV UNIV_POINT UNZIP UNZIP_FST UNZIP_SND UPDATE W
     WCR WF WFP WFREC WHILE WeakLinearOrder WeakOrder Wellfounded ZERO
     ZERO_REP ZIP ZRECSPACE \/ \\ _ inject_number adjacent antisymmetric
     approx bool_size case chooser combinpp.UPDATE common_prefixes count
     countable delN dest_rec diag diamond disjUNION divides dropWhile
     enumerate equiv_class equiv_on equivalence findi findq flip
     full_sum_size fupdLast iBIT_cases internal_mult inv inv_image invtri
     invtri0 irreflexive isPREFIX is_measure_maximal itself_case itself_size
     lift2 listRel list_CASE list_size literal_case longest_prefix measure
     min_pair_size mk_rec nat_elim__magic nf nfst npair nsnd nub num_CASE
     num_to_pair o oEL oHD one one_CASE one_size option_ABS option_CASE
     option_REP option_size pair_CASE pair_size pair_to_num pairwise part
     partition partitions prime rcdiamond refines reflexive relinv
     schroeder_close set setFST setL setR setSND some splitAtPki stmarker
     sum_CASE sum_size symmetric the_fun the_value total transitive tri
     trichotomous tri⁻¹ unint univ wellfounded ~ ¬ ² ³ Π ∅ ∅ᵣ ∑ ≠ 𝕌 𝕌ᵣ
-->
This section gives some help on assigning meaning to symbols:
```
   Overloading:
       <won't print>    ->  λ(x :α). list$CONS x (list$NIL :α list)
                            λ(h :α) (l :α list).
                                bool$~ (bool$IN h (list$LIST_TO_SET l))
                            λ(x :α itself). 𝕌(:α)
     %%                 ->  arithmetic$CEILING_MOD
     &                  ->  arithmetic$nat_elim__magic
     ()                 ->  one$one
     **                 ->  arithmetic$EXP
     *,                 ->  numpair$npair
     ++                 ->  (list$APPEND :α list -> α list -> α list)
     +++                ->  (sum$SUM_REL :(α -> β -> bool) ->
                                          (γ -> δ -> bool) ->
                                          α + γ -> β + δ -> bool)
     <<=                ->  λ(x :α list) (y :α list). list$isPREFIX x y
     <=/=>              ->  λ(x :bool) (y :bool). bool$~ (min$= x y)
     <=>                ->  (min$= :bool -> bool -> bool)
     <>                 ->  λ(x :α) (y :α). bool$~ (min$= x y)
     ALL_EL             ->  (list$EVERY :(α -> bool) -> α list -> bool)
     APPLICATIVE_FAPPLY ->  (list$LIST_APPLY :(α -> β) list ->
                                              α list -> β list)
                            (option$OPTION_APPLY :(α -> β) option ->
                                                  α option -> β option)
     BUTFIRSTN          ->  (list$DROP :num -> α list -> α list)
     BUTLAST            ->  (list$FRONT :α list -> α list)
     COUNTABLE          ->  (pred_set$countable :(α -> bool) -> bool)
     EVERY2             ->  (list$LIST_REL :(α -> β -> bool) ->
                                            α list -> β list -> bool)
     FIRSTN             ->  (list$TAKE :num -> α list -> α list)
     INFINITE           ->  λ(s :α -> bool). bool$~ (pred_set$FINITE s)
     IS_EL              ->  λ(x :α) (l :α list).
                                bool$IN x (list$LIST_TO_SET l)
     IS_PREFIX          ->  λ(x :α list) (y :α list). list$isPREFIX y x
     Id                 ->  (min$= :α -> α -> bool)
     MEM                ->  λ(x :α) (l :α list).
                                bool$IN x (list$LIST_TO_SET l)
     NOTIN              ->  λ(x :α) (y :α -> bool). bool$~ (bool$IN x y)
     OPTION_MAP2        ->  (option$OPTION_MAP2 :(α -> β -> γ) ->
                                                 α option ->
                                                 β option -> γ option)
                            (option$OPTION_MAP2 :(β -> γ -> α) ->
                                                 β option ->
                                                 γ option -> α option)
     PAIR_REL           ->  (pair$RPROD :(α -> β -> bool) ->
                                         (γ -> δ -> bool) ->
                                         α # γ -> β # δ -> bool)
     PERMUTES           ->  λ(f :α -> α) (s :α -> bool). pred_set$BIJ f s s
     PI                 ->  (pred_set$PROD_IMAGE :(α -> num) ->
                                                  (α -> bool) -> num)
     RELPOW             ->  (arithmetic$NRC :(α -> α -> bool) ->
                                             num -> α -> α -> bool)
     REMPTY             ->  (relation$EMPTY_REL :α -> α -> bool)
     SIGMA              ->  (pred_set$SUM_IMAGE :(α -> num) ->
                                                 (α -> bool) -> num)
     SINGL              ->  λ(x :α). list$CONS x (list$NIL :α list)
     SOME_EL            ->  (list$EXISTS :(α -> bool) -> α list -> bool)
     Wellfounded        ->  (prim_rec$wellfounded :(α -> α -> bool) -> bool)
     \\                 ->  arithmetic$CEILING_DIV
                            (relation$RDOM_DELETE :(α -> β -> bool) ->
                                                   α -> α -> β -> bool)
     _ inject_number    ->  arithmetic$nat_elim__magic
     case               ->  (list$list_CASE :α list ->
                                             β -> (α -> α list -> β) -> β)
                            (option$option_CASE :α option ->
                                                 β -> (α -> β) -> β)
                            (sum$sum_CASE :α + β -> (α -> γ) -> (β -> γ) -> γ)
                            (prim_rec$num_CASE :num -> α -> (num -> α) -> α)
                            (pair$pair_CASE :α # β -> (α -> β -> γ) -> γ)
                            (bool$itself_case :α itself -> β -> β)
                            (bool$literal_case :(α -> β) -> α -> β)
                            (bool$COND :bool -> α -> α -> α)
     combinpp.UPDATE    ->  (combin$UPDATE :α -> β -> (α -> β) -> α -> β)
     equiv_class        ->  λ(R :α -> β -> bool) (s :β -> bool) (x :α).
                                pred_set$GSPEC
                                  (λ(y :β).
                                       pair$, y
                                         (bool$/\ (bool$IN y s) (R x y)))
     flip               ->  (combin$C :(α -> β -> γ) -> β -> α -> γ)
     lift2              ->  (option$OPTION_MAP2 :(α -> β -> γ) ->
                                                 α option ->
                                                 β option -> γ option)
     listRel            ->  (list$LIST_REL :(α -> β -> bool) ->
                                            α list -> β list -> bool)
     relinv             ->  (relation$inv :(α -> β -> bool) -> β -> α -> bool)
     set                ->  (list$LIST_TO_SET :α list -> α -> bool)
     setFST             ->  pair$PAIR_SET (min$= :α -> α -> bool)
                              (combin$K (λ(x :α). bool$F) :β -> α -> bool)
     setL               ->  sum$SUM_SET (min$= :α -> α -> bool)
                              (combin$K (λ(x :α). bool$F) :β -> α -> bool)
     setR               ->  sum$SUM_SET
                              (combin$K (λ(x :β). bool$F) :α -> β -> bool)
                              (min$= :β -> β -> bool)
     setSND             ->  pair$PAIR_SET
                              (combin$K (λ(x :β). bool$F) :α -> β -> bool)
                              (min$= :β -> β -> bool)
     tri⁻¹              ->  numpair$invtri
     univ               ->  λ(x :α itself). 𝕌(:α)
     ¬                  ->  bool$~
     ²                  ->  λ(x :num). arithmetic$EXP x (2n :num)
     ³                  ->  λ(x :num). arithmetic$EXP x (3n :num)
     Π                  ->  (pred_set$PROD_IMAGE :(α -> num) ->
                                                  (α -> bool) -> num)
     ∅                  ->  (pred_set$EMPTY :α -> bool)
     ∅ᵣ                 ->  (relation$EMPTY_REL :α -> α -> bool)
     ∑                  ->  (pred_set$SUM_IMAGE :(α -> num) ->
                                                 (α -> bool) -> num)
     ≠                  ->  λ(x :α) (y :α). bool$~ (min$= x y)
     𝕌                  ->  λ(x :α itself). 𝕌(:α)
     𝕌ᵣ                 ->  (relation$RUNIV :α -> β -> bool)
   User printing functions:
     if gd then tr else fl       ->  bool.COND
     f⦇k ↦ v⦈       ->  combin.updpp
     LET f x       ->  bool.LET
     HIDDEN: s       ->  hide-printer
     GSPEC f       ->  pred_set.GSPEC
     𝕌(:α)       ->  pred_set.UNIV: term_grammar.grammar
```


<!-- term grammar with explanation -->

## Unicode 

With a properly configured terminal connection, vim and font installation, the
editor will display the above Unicode symbols properly. But there is a
question: how to enter these Unicode symbols.

In hol-vim, these symbols can be entered
through digraphs. See the character combinations for them in 
[holabs.vim](https://github.com/HOL-Theorem-Prover/HOL/blob/develop/tools/vim/holabs.vim) in HOL4's github repository. To enter mathematical symbols with digraphs, we need to push CTRL-K and then the two-letter digraph.
See a full list of mathematical Unicode characters in hol-vim and their corresponding digraphs:
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
