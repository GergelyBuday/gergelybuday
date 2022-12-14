---
layout: post
title:  "The HOL4 Syntax"
date:   2022-11-9 
categories: hol4
permalink: the-hol4-syntax
---

## Introduction

<q>It's just syntax</q>, said once a trained mathematician, and this has a grain of truth. Different higher-order theorem provers
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
With `open` we can refer to existing HOL4 libraries. For an extensive documentation of libraries, see 
the [HOL Reference Page](https://hol-theorem-prover.org/kananaskis-14-helpdocs/help/HOLindex.html). 

There are two main modes of using HOL4, the interactive mode that is helped with the hol-vim, emacs hol mode or the Visual Studio Code extension, and the batch mode, that is, running your script files through Holmake. In the interactive mode
you should load these libraries by hand, in batch mode it is done automatically. To do so interactively, one must use the keyword `load`, but
the user interfaces derive the component list from the `open` declaration. The interactive mode is a read-eval-print-loop
of the underlying SML compiler. The user interfaces are using this interactive loop.

The command `new_theory` defines the name of the theory and starts the session. The file name's prefix should coincide with the string given here, otherwise you get an error message. So here my file is `trivialScript.sml`.

The file ends with `export_theory`, which closes the session started with `new_theory`. Running Holmake will create a file that can be used from other script files, the same way as we imported system libraries with "open". <!-- This line is not clear -->

Between these there is a theorem and its proof in a Theorem-Proof-QED block. These keywords should start at the beginning of the line. We should give a name to the theorem, afterwards we can refer to it by this name. After `theorem`, we can give the goal we would like to prove, and after `Proof`, one can write the tactic that is meant to prove the goal.

## Definitions

The following user-friendly syntax elements are mentioned in the Description index as <q>special syntactic 
forms for scripts </q> .

### Datatypes

A datatype is an algebraic type, familiar from functional languages. For a binary tree, we can write
```
Datatype `bintree = Leaf | Node bintree 'a bintree`
```
in HOL4, which is the equivalent of 
```
datatype 'a bintree = Leaf | Node of 'a bintree * 'a * 'a bintree
```
in Standard ML. As we can see, the HOL4 definition is more terse. Be aware of the use of backticks for the Datatype definition in HOL4. An alternative HOL4 syntax is
```
Datatype: btree = LEAF | NODE btree 'a btree
End
```
As before, the `Datatype` and `End?? keywords should start their lines.

### Recursive Functions

Defining a recursive function has this syntax:
```
Definition fibonacci_def:
  (fib 0 = 0) ???
  (fib 1 = 1) ???
  (fib n = fib (n-2) + fib (n-1))
End
```
As usual, the order of patterns matter, the first has precedence over the others, and so on. Also usual is the position of Definition and End at the start of the line.

When the system cannot prove automatically that the function definition always terminates, so the function is total, we need to submit a termination proof. Its syntax involves the keyword `Termination` at the beginning of a line following the function definition:

```
Definition qsort_def:
  (qsort ord [] = []) /\
  (qsort ord (h::t) =
    qsort ord (FILTER (\x. ord x h) t) ++ [h] ++
    qsort ord (FILTER (\x. ~(ord x h)) t))
Termination
  WF_REL_TAC `measure (LENGTH o SND)` THEN cheat
End
```

### Inductive Relations

For defining inductive relations the syntax is:
```
Inductive Even:
  even 0 ???
  ???n. even n ??? even (n+2)
End
```

### Records

We can define records as 

```
Datatype: person = <| employed : bool ; age : num ; name : string |>
End
```
 and for a value let's have
```
<| age := 21; employed := F; name := "Layabout" |>
```
For field access, `person_age` is the syntax. For field update, `bob with employed updated_by f` is written, where f is the function
that is used for a new value of the field `employed`.

### Case expressions
Case expressions are for pattern matching:
```
case n of
  0 => "none"
| 1 => "one"
| 2 => "two"
| _ => "many"
```
### Type abbreviations

Compound types can be abbreviated with the new syntax:
```
Type set = ???:???a -> bool???
```
This is an input-only syntax if used this way. However, if you use the attribute `pp`, which is for pretty-printing, then HOL4 will print the type abbreviation in its output properly:
```
Type set[pp] = ???:???a -> bool???
```

### Triviality

For locally important theorems, we can use an attribute local for Theorem definitions:
```
Theorem fermat[local]:
```
These are not exported, only used locally. The user-friendly syntax for this is
```
Triviality fermat:
```
with the usual `Proof` and `QED`.

### Overloading

For overloading, there is the syntax
```
Overload "%%" = ???CEILING_MOD???;
```

## Types

<!-- type grammar with explanation -->

HOL4 gives us its type grammar with the command `type_grammar`:
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
     (??, ??) fun       = (??, ??) min$fun
     ind              = min$ind
     ?? itself         = ?? bool$itself
     ?? list           = ?? list$list
     num              = num$num
     one              = one$one                [not printed]
     ?? option         = ?? option$option
     (??, ??) prod      = (??, ??) pair$prod
     ?? recspace       = ?? ind_type$recspace
     ?? set            = (??, min$bool) min$fun  [not printed]
     (??, ??) sum       = (??, ??) sum$sum
     unit             = one$one               : type_grammar.grammar

```
We start by covering the non-standard notation. At the beginning we see the notation for function, sum and record types, with record type being the somewhat unusual hash mark, not
the standard star in SML. All these are right-associative (i.e. `A op B op C` means `A op (B op C)`). The `ind` type is the one for individuals, as we know it in formal logic. For any type, `??` itself is a one-element type whose element represents the type. Its role is technical in building more complex types like the fixed width word type. The type `num` is the type of natural numbers. The type `one` is the same as the unit type with the only element (). Type `?? recspace` is again a technical type used in the type definition package, holding finitely branching recursive types built from subsets of `??`. For an expert description see 
[an old mail of John Harrison](https://hol-info.narkive.com/ozgDo69L/recspace).

# Type variables 
For input syntax, type variables are possibly a prime followed by an alphanumeric string: `'a 'foo 'A11`. A prime followed by a single lower case latin letter is translated to a lowercase greek letter in output. Lambda is omitted, because of its special status in higher order logic, namely, the lambda operator. 
The input syntax `'l` is translated to `??`, and so on, until `'y`. Directly entering lowercase greek letters is
also possible. Caveat: do not use the leading prime for them.

# Type constraint

You might need a leading space before a type constraint so the system would not try to interpret the leading colon as part of the previous symbol:
```
$= :bool->bool->bool
```


## Lexing 

HOL4 variable names should be identifiers: 
- alphanumerics with leading letter and possibly underscores inside
- symbolic ASCII and Unicode identifiers: not letter and not digit Unicode characters are regarded as symbolic

# Dollar

The dollar has a number of uses: single $ is a low-precedence right-associative function application operator borrowed from Haskell: FACT $ SUC $ 2 + 3 = FACT(SUC(2+3)) .
Starting with $ only $-only symbolic identifiers are possible: $, \$$, \$\$$ ... . We can get rid of infix and other special syntax status of identifiers with a prefixing dollar: $< . Without $ HOL4 gives an error message, but this works:

```
> type_of ``$<``;
val it = ???:num -> num -> bool???: hol_type
```
This is useful when we want to use the function as an argument. An alternative syntax for this is using parentheses: (<).

 Last, $ is used as a separator between theory name and identifier, forming a long identifier: bool$COND .

# Non-aggregeting characters

Characters in this class, unless there is a symbolic identifier defined with them, are lexed separately: parentheses, curly braces and square brackets: () {} [], tilde, dot, comma, semicolon and hyphen: ~ . , ; - . So, (( +; and -+ are treated as two characters. Non-aggregating Unicode characters are:
```
?? U+00AC ??? U+27E8
??? U+2308 ??? U+27E9
??? U+2309 ??? U+2983
??? U+230A ??? U+2984
??? U+230B ??? U+2987
??? U+27E6 ??? U+2988
??? U+27E7
```
# Whitespace

Space, Carriage Return, Line Feed, Tab and Form Feed are separators. 

# Numbers

A string of digits is a number. The underscore is a pseudo-digit to give spacing if needed: 3\_000\_000 .
There is postfix notation for the num and the int type: 3n, 3i .
For hexadecimal and binary numbers there are prefixal forms 0xAF12 and 0b1110 . For hexadecimals, besides A-F, lowercase a-f can be used as well.

# Comments

Comments are written with standard SML delimiters: (* This is a comment *)

## Parsing

In functional programming, interesting data structures are built using the constructors of data types. But, of course, it would be cumbersome to write
```
APP (APP (APP (IDENT "COND", IDENT "P"), IDENT "Q"), IDENT "R")
```
instead of 
```
if P then Q else R
```

# Overloading

HOL4 maintains an overload map from strings to lists of terms for parsing, and another one in the
opposite direction for prettyprinting: from lists of terms to identifiers . This allows to use + for natural numbers, integers and words. Naturally, the use of overloaded terms might require type constraints.

# Functions with special syntax

Functions mostly use curried postfix syntax for arguments: f x y z for a three-argument function f.
But there is a possibility to use binder, prefix, suffix, infix, closefix and mixfix syntax.

A binder binds a variable. Technically, due to Church, this is done on applying a binder constant to a lambda abstraction. So ???x.M is ???(\\x.M) . Consecutive application of the same binder can be shorthanded with only one instance of the binder: ???x y z.M .

Infix operator op works as A op B. It can be left-associative, right-associative or non-associative.

For prefix operations, standard function application is a good example: f x .

Relation closures are good examples of suffix operators: R^+ for transitive closure of R.

Closefix operators are for delimiters: we can use [\| x \|] for a denotation semantics of x .

For mixfix syntax, the if-then-else clause and the [ t1 / t2 ] t3 notation for term 
substitution is a good example.

# Quotation and antiquotation

Quotations are of type 'a frag list and have the concrete syntax delimited with backticks: \`f x = 3\`.
Parse.Term is of type term quotation -> term and it creates a term of a quotation.

A direct way of constructing such a term is to use double quotations: \`\`f x = 3\`\` . If the expression is meant to be a type, then it should begin with a colon: \`\`:'a -> bool\`\`.

An advantage of quotations is the free use of newlines and backslash characters.

The escape character in quotations is the caret: ^ . The ^(t) syntax is for antiquotations: its aim
is to embed ML type or term expressions. If the expression is an ML identifier, then the parentheses
can be ommitted altogether.

# Term grammar

So HOL4 has a parser that translates the surface syntax into primitive constructors. Similarly to type\_grammar, function term\_grammar gives us the current state of the grammar used in parsing. I inject explanations to the output of the command to make it understandable.
```
> term_grammar();
val it =
   (0)    TM  ::= "OLEAST" <..binders..> "." TM
                | "LEAST" <..binders..> "." TM | "some" <..binders..> "." TM
                | "???!" <..binders..> "." TM [?!] | "?!" <..binders..> "." TM
                | "???" <..binders..> "." TM [?] | "?" <..binders..> "." TM
                | "???" <..binders..> "." TM [!] | "!" <..binders..> "." TM
                | "@" <..binders..> "." TM | "??" <..binders..> "." TM
                | "\" <..binders..> "." TM
```
First, binders. If c is a binder, c x. t translates to $c \\x.t, that is, the standard syntax version of
the binder applied to the lambda abstraction  ??x.t . Also, c x1 x2 .. xN . t translates to c x1. c x2. .. c xN . t .

The LEAST binder works on functions defined for natural numbers, giving back the least number that satisfies its argument predicate: ???P. $LEAST P = WHILE ($?? ??? P) SUC 0 . The while loop starts from 0 and goes until a successor satisfies predicate P. The binder OLEAST is an option valued binder that gives SOME n when LEAST would define a concrete value and NONE otherwise: ???P. $OLEAST P = if ???n. P n then SOME (LEAST n. P n) else NONE .

To explain "some", take binder @, which is a higher order version of Hilbert's choice operator ??, an element that satisfies a predicate P, given there is such an element: ???x.P x ??? P(@x.P x) . The binder some (not to mistake for the SOME constructor of the option type) is ???P. $some P = if ???x. P x then SOME (@x. P x) else NONE, it tells us whether the choice operator would return a real value satisfying the relation.

Then comes the uniquely exists quantor ???! and its ASCII counterpart ?!, the exists quantor ??? and its ASCII version ?, the universal quantor ??? and ASCII !, the lambda operator ?? and its ASCII equivalent \\ .
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
Restricted quantification is giving a bounding set for the values of the bound variable: (\\ x :: P. M) = M[y/x] only if y ??? P. Binder argument concatenation is the case I described above: we can write only one binder with a list of bound variables. The let construct is let v = M in N. The left-associative "and" construct is the one we can use in a let expression: let v = M and u = P in N. The arrow => is the mapping of a value to a pattern in a case construction, see the previous HOL4 example.
```
   (50)   TM  ::= TM "," TM     (R-associative)
   (70)   TM  ::= "if" TM "then" TM "else" TM  [COND]
   (80)   TM  ::= TM ":-" TM     (non-associative)
   (100)  TM  ::= TM "???" TM  [  combinpp.leftarrow]
                | TM "|->" TM  [  combinpp.leftarrow] | TM "???" TM  [<=/=>]
                | TM "<=/=>" TM   | TM "???" TM  [<=>] | TM "<=>" TM
                    (non-associative)
   (200)  TM  ::= TM "???" TM  [==>] | TM "==>" TM     (R-associative)
```
The right-associative comma is the pair constructor. There's no need for an explanation of the if-then-else construct that translates to the COND internal primitive, as seen above. An input syntax for the turnstile logical symbol is :- . It is used only in low-level definitions. The maplet symbol ??? and its ASCII equivalent |-> is the finite map type operator. For logical equivalence and non-equivalence, there is ??? and ???, and their ASCII counterpart <=> and <=/=> . For logical implication there is
??? and the ASCII ==> .
```
   (300)  TM  ::= TM "???" TM  [\/] | TM "\/" TM     (R-associative)
   (310)  TM  ::= TM ":>" TM     (L-associative)
   (320)  TM  ::= TM "=+" TM  [UPDATE]   (non-associative)
   (400)  TM  ::= TM "???" TM  [/\] | TM "/\" TM     (R-associative)
   (425)  TM  ::= TM "refines" TM   | TM "partitions" TM
                | TM "equiv_on" TM   | TM "???" TM  [NOTIN] | TM "NOTIN" TM
                | TM "???" TM  [IN] | TM "IN" TM
                    (non-associative)
```
There is ??? for logical or and its ASCII equivalent \/ . The :> operator is reverse function application: x :> f is f x. And it lets us write x :> g :> f for f(g(x)) . The =+ symbol is function update: (a =+ b) f updates f with value b at argument a . For logical and there is ??? and its ASCII counterpart /\ . For two set of sets, A refines B if for every element set of A there is an element of B so that the former is a subset of the latter: for a ??? A there is b ??? B so that a ??? b . The infix equiv_on operator tells that a relation R is an equivalence relation on the underlying set S, that is, R is reflexive, symmetric and transitive. The expression X partitions Y holds when X is a set of sets, the partition of Y according to some equivalence relation R. For set membership and non-membership there is ??? and ??? and their ASCII notation IN and NOTIN .

```
   (450)  TM  ::= TM "???" TM  [<<=] | TM "<<=" TM   | TM "PERMUTES" TM
                | TM "HAS_SIZE" TM   | TM "???" TM  [PSUBSET]
                | TM "PSUBSET" TM   | TM "???" TM  [SUBSET] | TM "SUBSET" TM
                | TM "???" TM  [>=] | TM ">=" TM   | TM "???" TM  [<=]
                | TM "<=" TM   | TM ">" TM   | TM "<" TM
                | TM "??????" TM  [RSUBSET] | TM "RSUBSET" TM   | TM "???" TM
                | TM "<>" TM   | TM "=" TM
                    (non-associative)
```
The unicode symbol ??? and its ASCII version &lt;&lt;= is for the list prefix partial order isPREFIX . 
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
   (480)  TM  ::= TM "???" TM  [++] | TM "++" TM   | TM "+++" TM
                    (L-associative)
   (490)  TM  ::= TM "::" TM  [CONS] | TM "INSERT" TM
                | TM "###" TM  [PAIR_REL] | TM "LEX" TM   | TM "##" TM
                    (R-associative)
```
The ASCII double plus, ++ operator and its Unicode variant ??? is list append. The triple plus +++ is an operator on relations: its type is
:(?? -> ?? -> bool) -> (?? -> ?? -> bool) -> ?? + ?? -> ?? + ?? -> bool, so it creates a componentwise sum type for the two relations.

The double colon :: is the cons operation as suggested: extending a list with an element on the left. The keyword INSERT is set insertion:
1 INSERT {1;3} = {1;3} . The triple hash mark ### operates on two relations and gives back a relation that is of componentwise products of the
original relations' base types: :?? # ?? -> ?? # ?? -> bool , from :?? -> ?? -> bool and :?? -> ?? -> bool . 
```
   (500)  TM  ::= TM "???" TM  [disjUNION] | TM "<+>" TM  [disjUNION]
                | TM "DELETE" TM   | TM "DIFF" TM   | TM "???" TM  [UNION]
                | TM "UNION" TM   | TM "<*>" TM  [APPLICATIVE_FAPPLY]
                | TM "???" TM  [-] | TM "-" TM   | TM "+" TM
                | TM "??????" TM  [RUNION] | TM "RUNION" TM
                    (L-associative)
   (600)  TM  ::= TM "???" TM  [INTER] | TM "INTER" TM   | TM "\\" TM
                | TM "DIV" TM   | TM "*" TM   | TM "??????" TM  [RINTER]
                | TM "RINTER" TM
                    (L-associative)
   (601)  TM  ::= TM "??" TM  [CROSS] | TM "CROSS" TM   | TM "???" TM  [*,]
                | TM "*," TM
                    (R-associative)
```
The <+> and its Unicode counterpart ??? is disjoint union for relations: for types :?? -> bool and :?? -> bool it gets :?? + ?? -> bool. 
The infix operator DELETE deletes an element from a set. The next one, DIFF is set difference. The meaning of UNION and its Unicode variant
??? is obviously set union. The infix operator <\*>, nicknamed APPLICATIVE\_FAPPLY applies all functions in a function list to a list of arguments and concatenates the resulting lists: [(??x. x + 2); (??x. x + 4)] <*> [1; 2; 3] = [3; 4; 5; 5; 6; 7] . 

The Unicode minus sign seems to be just an alias to standard ASCII minus sign - . The ASCII plus + is addition for natural numbers, of type num.
The infix operator RUNION or its Unicode equivalent ?????? lifts set union operation to relations, and so does RINTER and ?????? for intersection. 
The infix INTER and its Unicode counterpart ??? is obviously set intersection. The infix \\\\ is an operator on finite maps, it removes the right argument from the domain of the finite map on the left.

The infix DIV is obviously natural number division, and ASCII star is natural number multiplication. The infix CROSS and its Unicode notation ?? creates a cross product of two sets, on other words, a set of pairs: :?? # ?? -> bool . Remember that hash mark # is for the product type. The infix ASCII *, operator on natural numbers and its Unicode variant ??? allows us to encode two natural numbers in one through triangular numbers. It is possible then to decode the first and second number from this encoded value.
```
   (650)  TM  ::= TM "%%" TM   | TM "MOD" TM     (L-associative)
   (700)  TM  ::= TM "**" TM   | TM "EXP" TM     (R-associative)
```
The symbolic identifier %% looks like a modulo operation before MOD but it is in fact a derived operation: CEILING_MOD m n = (n - m MOD n) MOD n .
MOD is the usual modulo operation. The standard EXP and its symbolic counterpart \*\* is natural number exponentiation. 
```
   (800)  TM  ::= TM "??????" TM  [O] | TM "O" TM   | TM "???" TM  [o]
                | TM "o" TM
                    (R-associative)
```
Capital O and its symbolic counterpart ?????? is relation compi??osition, while small o and Unicode ??? is function composition.
```
   (899)  TM  ::= TM ":" TY  (type annotation)
   (900)  TM  ::= "&" TM   | "-" TM  [numeric_negate] | "??" TM   | "~" TM
   (2000) TM  ::= TM TM  (function application)   (L-associative)
```
With a weak precedence, colon : is for type annotation. 
Ampersand, &, is for converting from num to int, provided integerTheory is loaded. It is also of internal use for nat\_elim\_\_magic.
The standard minus sign is numeric negation. The ASCII tilde ~ and its Unicode counterpart ?? is for boolean negation.
Function application, writing terms consecutively with only whitespace has a high precedence to allow one-argument function applications to write without parentheses.
```
   (2100) TM  ::= TM "??"   | TM "??"   | TM "???"  [relinv] | TM "^="  [EQC]
                | TM "???"  [RTC] | TM "^*"  [RTC] | TM "???"  [TC]
                | TM "^+"  [TC]
                | TM "???" LTM<  combinpp.nil,  combinpp.cons,;> "???"
                    [  combinpp.toplevelupd]
                | TM "(|" LTM<  combinpp.nil,  combinpp.cons,;> "|)"
                    [  combinpp.toplevelupd]
```
The superscripts ()?? and ()?? are obviously cubic and quadratic powers. The superscript T, Unicode ()??? is the inverse of a relation. 
The following are closures of a relation of type A x A , for it is meaningful if we can compose the relation with itself. Equality closure is ^=, 
reflexive transitive closure is ^* and Unicode ???, and transitive closure is ^+ or Unicode ()??? .

The delimiters (| and |) and their Unicode equivalent ??? and ??? are for function update: (\x.x) (| 2 |-> 3 |) creates a function that is the identity function on natural numbers, except that for argument 2 it gives back 3. And so does the Unicode notation (??x. x)???2 ??? 3??? .
```
   (2200) TM  ::= "????" TM   | "univ" TM
   (2500) TM  ::= TM "." TM  [record field selection]   (L-associative)
          TM  ::= "[" LTM<NIL,CONS,;> "]"  [ListForm<NIL,CONS>]
                | "{" LTM<EMPTY,INSERT,;> "}"  [ListForm<EMPTY,INSERT>]
                | "{" TM "|" TM "|" TM "}"  [gspec2 special]
                | "{" TM "|" TM "}"  [gspec special] | "(" ")"  [one]
                | "<|" LTM< _ record nil, _ record cons,;> "|>"
                    [ListForm< _ record nil, _ record cons>]
                | "(" TM ")"  [just parentheses, no term produced]
```
The identifier univ and Unicode ???? is for the universal set of a type. Its definition is ??? ????(:??) = (??x.T), in other words, any element of the type is an element of the universal set. The usual dot notation is for record
field selection, rec.fieldname . Square brackets with semicolons are for lists: type\_of ``[1;2;3]``; returns
???:num list???. Curly braces with semicolons are for concrete sets: type_of ``{1;2;3}``; returns ???:num -> bool???. Sets are modelled with their characteristic function on their base type. Curly braces with vertical bars allow us
to write set comprehensions: ??? ???s t. s DIFF t = {x | x ??? s ??? x ??? t} . The usual hermite () is the only element of type one and the isomorphic type unit.


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
     trichotomous tri????? unint univ wellfounded ~ ?? ?? ?? ?? ??? ?????? ??? ??? ???? ???????
-->
The next section gives some help on assigning meaning to symbols. I omit the already discussed symbolic identifiers and 
alphabetic identifiers that are easy to find in the source code. 

First, there are some spooky identifiers that wouldn't print:
```
   Overloading:
       <won't print>    ->  ??(x :??). list$CONS x (list$NIL :?? list)
                            ??(h :??) (l :?? list).
                                bool$~ (bool$IN h (list$LIST_TO_SET l))
                            ??(x :?? itself). ????(:??)
```
A properly constructed grep command gives us the empty string definitions for these:
```
$ grep 'overload_on.*""' -R HOL/src
HOL/src/pred_set/src/pred_setScript.sml:val _ = overload_on ("", ???\x:'a itself. UNIV : 'a set???)
HOL/src/list/src/listScript.sml:val _ = overload_on ("", ???\h:'a l:'a list. ~(h IN LIST_TO_SET l)???)
HOL/src/list/src/listScript.sml:val _ = overload_on("", ???\x:'a. [x]???)
```
The first thing in the term_grammar output that won't print is the [x] notation for having a one-element list, see the third line in grep output.

The second non-printing grammar element in the term grammar is the second in grep output. I give context to it in 
HOL/src/list/src/listScript.sml :

```
val _ = overload_on ("", ???\h:'a l:'a list. ~(h IN LIST_TO_SET l)???)
  (* last over load here causes the term ~(h IN LIST_TO_SET l) to not print
     using overloads.  In particular, this prevents the existing overload for
     NOTIN from firing in this type instance, and allows ~MEM a l to print
     because the pretty-printer will traverse into the negated term (printing
     the ~), and then the MEM overload will "fire".
  *)
```
So, ~MEM is expressing that an element does not appear in a list, converting the list to a set internally.

Digging the code for the third we meet a technicality in HOL/src/pred_set/src/pred_setScript.sml, the first hit in grep output:

```
val _ = overload_on ("univ", ``\x:'a itself. UNIV : 'a set``)
val _ = set_fixity "univ" (Prefix 2200)

val _ = overload_on (UnicodeChars.universal_set, ``\x:'a itself. UNIV: 'a set``)
val _ = set_fixity UnicodeChars.universal_set (Prefix 2200)
(* the overloads above are only for parsing; printing for this is handled
   with a user-printer.  (Otherwise the fact that the x is not bound in the
   abstraction produces ARB terms.)  To turn printing off, we overload the
   same pattern to "" *)
val _ = overload_on ("", ???\x:'a itself. UNIV : 'a set???)
```
so non-printing has an internal technical reason here: that is, pretty printing.

<!--
     %%                 ->  arithmetic$CEILING_MOD
     &                  ->  arithmetic$nat_elim__magic
     ()                 ->  one$one
     **                 ->  arithmetic$EXP
     *,                 ->  numpair$npair
     ++                 ->  (list$APPEND :?? list -> ?? list -> ?? list)
     +++                ->  (sum$SUM_REL :(?? -> ?? -> bool) ->
                                          (?? -> ?? -> bool) ->
                                          ?? + ?? -> ?? + ?? -> bool)
     <<=                ->  ??(x :?? list) (y :?? list). list$isPREFIX x y
     <=/=>              ->  ??(x :bool) (y :bool). bool$~ (min$= x y)
     <=>                ->  (min$= :bool -> bool -> bool)
     <>                 ->  ??(x :??) (y :??). bool$~ (min$= x y)
     ALL_EL             ->  (list$EVERY :(?? -> bool) -> ?? list -> bool)
     APPLICATIVE_FAPPLY ->  (list$LIST_APPLY :(?? -> ??) list ->
                                              ?? list -> ?? list)
                            (option$OPTION_APPLY :(?? -> ??) option ->
                                                  ?? option -> ?? option)
     BUTFIRSTN          ->  (list$DROP :num -> ?? list -> ?? list)
     BUTLAST            ->  (list$FRONT :?? list -> ?? list)
     COUNTABLE          ->  (pred_set$countable :(?? -> bool) -> bool)
     EVERY2             ->  (list$LIST_REL :(?? -> ?? -> bool) ->
                                            ?? list -> ?? list -> bool)
     FIRSTN             ->  (list$TAKE :num -> ?? list -> ?? list)
     INFINITE           ->  ??(s :?? -> bool). bool$~ (pred_set$FINITE s)
     IS_EL              ->  ??(x :??) (l :?? list).
                                bool$IN x (list$LIST_TO_SET l)
     IS_PREFIX          ->  ??(x :?? list) (y :?? list). list$isPREFIX y x
     Id                 ->  (min$= :?? -> ?? -> bool)
     MEM                ->  ??(x :??) (l :?? list).
                                bool$IN x (list$LIST_TO_SET l)
     NOTIN              ->  ??(x :??) (y :?? -> bool). bool$~ (bool$IN x y)
     OPTION_MAP2        ->  (option$OPTION_MAP2 :(?? -> ?? -> ??) ->
                                                 ?? option ->
                                                 ?? option -> ?? option)
                            (option$OPTION_MAP2 :(?? -> ?? -> ??) ->
                                                 ?? option ->
                                                 ?? option -> ?? option)
     PAIR_REL           ->  (pair$RPROD :(?? -> ?? -> bool) ->
                                         (?? -> ?? -> bool) ->
                                         ?? # ?? -> ?? # ?? -> bool)
     PERMUTES           ->  ??(f :?? -> ??) (s :?? -> bool). pred_set$BIJ f s s
     PI                 ->  (pred_set$PROD_IMAGE :(?? -> num) ->
                                                  (?? -> bool) -> num)
     RELPOW             ->  (arithmetic$NRC :(?? -> ?? -> bool) ->
                                             num -> ?? -> ?? -> bool)
     REMPTY             ->  (relation$EMPTY_REL :?? -> ?? -> bool)
     SIGMA              ->  (pred_set$SUM_IMAGE :(?? -> num) ->
                                                 (?? -> bool) -> num)
     SINGL              ->  ??(x :??). list$CONS x (list$NIL :?? list)
     SOME_EL            ->  (list$EXISTS :(?? -> bool) -> ?? list -> bool)
     Wellfounded        ->  (prim_rec$wellfounded :(?? -> ?? -> bool) -> bool)
-->
```
     \\                 ->  arithmetic$CEILING_DIV
                            (relation$RDOM_DELETE :(?? -> ?? -> bool) ->
                                                   ?? -> ?? -> ?? -> bool)
```
The symbolic identifier \\\\ overloads for two purposes: for the arithmetic CEILING\_DIV: 
CEILING_DIV m n = (m + (n - 1)) DIV n and
RDOM\_DELETE, which removes an element from the domain, i.e. the left supporting set of a relation.
<!--
     _ inject_number    ->  arithmetic$nat_elim__magic
     case               ->  (list$list_CASE :?? list ->
                                             ?? -> (?? -> ?? list -> ??) -> ??)
                            (option$option_CASE :?? option ->
                                                 ?? -> (?? -> ??) -> ??)
                            (sum$sum_CASE :?? + ?? -> (?? -> ??) -> (?? -> ??) -> ??)
                            (prim_rec$num_CASE :num -> ?? -> (num -> ??) -> ??)
                            (pair$pair_CASE :?? # ?? -> (?? -> ?? -> ??) -> ??)
                            (bool$itself_case :?? itself -> ?? -> ??)
                            (bool$literal_case :(?? -> ??) -> ?? -> ??)
                            (bool$COND :bool -> ?? -> ?? -> ??)
     combinpp.UPDATE    ->  (combin$UPDATE :?? -> ?? -> (?? -> ??) -> ?? -> ??)
     equiv_class        ->  ??(R :?? -> ?? -> bool) (s :?? -> bool) (x :??).
                                pred_set$GSPEC
                                  (??(y :??).
                                       pair$, y
                                         (bool$/\ (bool$IN y s) (R x y)))
     flip               ->  (combin$C :(?? -> ?? -> ??) -> ?? -> ?? -> ??)
     lift2              ->  (option$OPTION_MAP2 :(?? -> ?? -> ??) ->
                                                 ?? option ->
                                                 ?? option -> ?? option)
     listRel            ->  (list$LIST_REL :(?? -> ?? -> bool) ->
                                            ?? list -> ?? list -> bool)
     relinv             ->  (relation$inv :(?? -> ?? -> bool) -> ?? -> ?? -> bool)
     set                ->  (list$LIST_TO_SET :?? list -> ?? -> bool)
     setFST             ->  pair$PAIR_SET (min$= :?? -> ?? -> bool)
                              (combin$K (??(x :??). bool$F) :?? -> ?? -> bool)
     setL               ->  sum$SUM_SET (min$= :?? -> ?? -> bool)
                              (combin$K (??(x :??). bool$F) :?? -> ?? -> bool)
     setR               ->  sum$SUM_SET
                              (combin$K (??(x :??). bool$F) :?? -> ?? -> bool)
                              (min$= :?? -> ?? -> bool)
     setSND             ->  pair$PAIR_SET
                              (combin$K (??(x :??). bool$F) :?? -> ?? -> bool)
                              (min$= :?? -> ?? -> bool)
-->
```
     tri?????              ->  numpair$invtri
```
The Unicode superscript -1 is the inverse of the triangle number function defined in 
HOL/src/num/extra_theories/numpairScript.sml .
<!--
     univ               ->  ??(x :?? itself). ????(:??)
     ??                  ->  bool$~
     ??                  ->  ??(x :num). arithmetic$EXP x (2n :num)
     ??                  ->  ??(x :num). arithmetic$EXP x (3n :num)
-->
```
     ??                  ->  (pred_set$PROD_IMAGE :(?? -> num) ->
                                                  (?? -> bool) -> num)
     ???                  ->  (pred_set$EMPTY :?? -> bool)
     ??????                 ->  (relation$EMPTY_REL :?? -> ?? -> bool)
     ???                  ->  (pred_set$SUM_IMAGE :(?? -> num) ->
                                                 (?? -> bool) -> num)
```
Capital Pi is the usual product on natural numbers, whose first argument is a number-valued function on domain ?? that is corresponding to the formula, and the second argument is the characteristic function on the same domain 
?? representing the set the production goes over.

Unicode ??? and ?????? is for the empty set and the empty relation, respectively.

Capital Sigma is similar in its arguments to Pi, but this is for summing natural numbers.
<!--
     ???                  ->  ??(x :??) (y :??). bool$~ (min$= x y)
     ????                  ->  ??(x :?? itself). ????(:??)
     ???????                 ->  (relation$RUNIV :?? -> ?? -> bool)
   User printing functions:
     if gd then tr else fl       ->  bool.COND
     f???k ??? v???       ->  combin.updpp
     LET f x       ->  bool.LET
     HIDDEN: s       ->  hide-printer
     GSPEC f       ->  pred_set.GSPEC
     ????(:??)       ->  pred_set.UNIV: term_grammar.grammar
-->


<!-- term grammar with explanation -->

## Unicode 

With a properly configured terminal connection, vim and font installation, the
editor will display the above Unicode symbols properly. But there is a
question: how to enter these Unicode symbols.

In hol-vim, these symbols can be entered
through digraphs. See the character combinations for them in 
[holabs.vim](https://github.com/HOL-Theorem-Prover/HOL/blob/develop/tools/vim/holabs.vim) in HOL4's github repository. To enter mathematical symbols with digraphs, we need to push CTRL-K and then the two-letter digraph.
Here is a full list of mathematical Unicode characters in hol-vim and their corresponding digraphs:
```
??? AN conjunction
??? OR disjunction
?? NO -, negation
??? => implication
??? =< less or equal
??? >= greater or equal
??? == bi-implication, if and only if
??? != not equal
??? FA universal quantor, for all
??? TE existential quantor, exists
?? l* the lambda operator
??? (- element of
+ (+ not an element, this did not work,
     use ^Vu2209 instead for ???, HOL4 will understand it
??? (U meet of sets
??? U) union of sets
??? (_ subset (might be equal)
??? (C proper subset (cannot be equal)
```
