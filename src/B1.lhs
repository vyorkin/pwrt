
**Implication** and **if-and-only-if** operators.

> module B1 where

`==>` and `<=>` are special operators.

`==>` is the **implication** operator,
think of it as the following Haskell function:

< {-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
< (==>) :: Bool -> Bool -> Bool
< False ==> False = True
< False ==> True  = True
< True  ==> True  = True
< True  ==> True  = False

`<=>` is the **if-and-only-if** operator,
which is equivalent to the Haskell function:

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
 these **VC**s are valid.
