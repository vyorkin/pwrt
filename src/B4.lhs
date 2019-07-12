

Lifting functions to Measures.

> module B4 where
> import A1 (safeDiv)

> notEmpty :: [a] -> Bool
> notEmpty []    = False
> notEmpty (_:_) = True

Measure is a _total_ Haskell function:

* single equation per data constructor
* guaranteed to _terminate_

**measure** tells LiquidHaskell to _lift_ a
function into the refinement logic:

> {-@ measure notEmpty @-}

Now we can use the `notEmpty` predicate to
describe non-empty lists:

> {-@ type NEList a = { v:[a] | notEmpty v } @-}

`size` returns a non-zero value _if_ the input list is
not-empty. We capture this condition with an implication in the
output refinement.

> {-@ size :: xs:[a] -> { v:Nat | notEmpty xs => v > 0 } @-}
> size :: [a] -> Int
> size []     = 0
> size (_:xs) = 1 + size xs

> {-@ average :: NEList Int -> Int @-}
> average :: [Int] -> Int
> average xs = total `safeDiv` elems
>   where
>     total = sum xs
>     elems = size xs

Ex 6.1 (Average, Maybe)

Ex 6.2 (Debugging specificatins)
