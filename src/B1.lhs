
**Implication** and **if-and-only-if** operators.

> module B1 where

`==>` and `<=>` are special operators.

`==>` is the **implication** operator,
equivalent the following Haskell function:

> infixr 7 ==>
> {-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
> (==>) :: Bool -> Bool -> Bool
> False ==> False = True
> False ==> True  = True
> True  ==> True  = True
> True  ==> False = False

`<=>` is the **if-and-only-if** operator,
which is equivalent to the Haskell function:

> infixr 7 <=>
> {-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
> (<=>) :: Bool -> Bool -> Bool
> False <=> False = True
> False <=> True  = False
> True  <=> True  = True
> True  <=> False = False

An **environment** is a mapping from variables to their Haskell types.
For example, let `G` be an environment:

< x :: Int
< y :: Int
< z :: Int

Satisfaction:

A **predicate** is SATISFIABLE in a env `G` if _there exists_
an **assignment** in `G` that makes the **predicate** evaluate
to `True`.

< x + y == z

Validity:

A **predicate** is VALID in an env `G` if _every_ **assignment**
make a **predicate** evalue to `True`.

< x < 10 || x == 10 || x > 10

Verification conditions:

LH checks the program in roughly 2 steps:

1. Combines code and types down to a set of _Verification
 Conditions (VC)_ which are **predicates** that are valid _only
 if_ the program satisfies a given property which are
 **predicates** that are valid _only if_ the program satisfies a
 given property.

2. Quries the **SMT solver** (e.g. `Z3`) to determine whether
 these **VC**'s are valid.

Examples (Prepositions).

Here `TRUE` is a _refined type_ for `Bool` valued expressions
that _always_ evaluate to `True`:

> {-@ type TRUE = {v:Bool | v} @-}

Same with `FALSE`:

> {-@ type FALSE = {v:Bool | not v} @-}

Lets see some examples:

Valid:

> {-@ ex0 :: TRUE @-}
> ex0 :: Bool
> ex0 = True

Invalid:

< {-@ ex0' :: TRUE @-}
< ex0' :: Bool
< ex0' = False

Valid:

> {-@ ex1 :: Bool -> TRUE @-}
> ex1 :: Bool -> Bool
> ex1 b = b || not b

Valid as well:

> {-@ ex2 :: Bool -> FALSE @-}
> ex2 :: Bool -> Bool
> ex2 b = b && not b

Examples with `==>` operator.

Read `p ==> q` as: _if `p` is `true` then `q` must also be `true`.

> {-@ ex3 :: Bool -> Bool -> TRUE @-}
> ex3 :: Bool -> Bool -> Bool
> ex3 a b = (a && b) ==> a

> {-@ ex4 :: Bool -> Bool -> TRUE @-}
> ex4 :: Bool -> Bool -> Bool
> ex4 a b = (a && b) ==> b

Ex 2.1:

> {-@ ex3' :: Bool -> Bool -> TRUE @-}
> ex3' :: Bool -> Bool -> Bool
> ex3' a _ = (a || a) ==> a

Modus ponens:

> {-@ ex6 :: Bool -> Bool -> TRUE @-}
> ex6 :: Bool -> Bool -> Bool
> ex6 a b = (a && (a ==> b)) ==> b

> {-@ ex7 :: Bool -> Bool -> TRUE @-}
> ex7 :: Bool -> Bool -> Bool
> ex7 a b = a ==> (a ==> b) ==> b

De Morgan's laws:

> {-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
> exDeMorgan1 :: Bool -> Bool -> Bool
> exDeMorgan1 a b = not (a || b) <=> (not a && not b)

> {-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
> exDeMorgan2 :: Bool -> Bool -> Bool
> exDeMorgan2 a b = not (a && b) <=> (not a || not b)

Examples: Arithmetic

Ok:

> {-@ ax0 :: TRUE @-}
> ax0 :: Bool
> ax0 = 1 + 1 == 2

Not ok:

< {-@ ax0' :: TRUE @-}
< ax0' :: Bool
< ax0' = 1 + 1 == 3

Via the laws of arithmetic, it is equivalent to `0 < 1`,
which is `True` independent of the value of `x`.

> {-@ ax1 :: Int -> TRUE @-}
> ax1 :: Int -> Bool
> ax1 x = x < x + 1

We can combine arithmetic and prepositional operators:

> {-@ ax2 :: Int -> TRUE @-}
> ax2 :: Int -> Bool
> ax2 x = (x < 0) ==> (0 <= 0 - x)

> {-@ ax3 :: Int -> Int -> TRUE @-}
> ax3 :: Int -> Int -> Bool
> ax3 x y = (0 <= x) ==> (0 <= y) ==> (0 <= x + y)

> {-@ ax4 :: Int -> Int -> TRUE @-}
> ax4 :: Int -> Int -> Bool
> ax4 x y = (x == y - 1) ==> (x + 2 == y + 1)

> {-@ ax5 :: Int -> Int -> Int -> TRUE @-}
> ax5 :: Int -> Int -> Int -> Bool
> ax5 x y z =   (x <= 0 && x >= 0)
>           ==> (y == x + z)
>           ==> (y == z)

Ex 2.3:

> {-@ ax6 :: Int -> Int -> TRUE @-}
> ax6 :: Int -> Int -> Bool
> ax6 x y = False ==> (x <= x + y)

Examples: Uninterpreted function

SMT solver doesn't know how functions are defined. It only knows
the _axiom of conguence_: any function `f` returns equal
outputs when invoked on equal inputs.

Lets define an uninterpreted function from `Int` to `Int`:

> {-@ measure f :: Int -> Int @-}

We test the axiom by checking the following predicate:

< {-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
< congruence :: (Int -> Int) -> Int -> Int -> Bool
< congruence f x y = (x == y) ==> (f x == f y)
