
Case study: **Insertion Sort**.

> {-# LANGUAGE ScopedTypeVariables #-}
> {-@ LIQUID "--no-termination" @-}

> module A3 where

> import A1 (impossible)
> import A2 (List(..), length)
> import Data.Set (Set)
> import qualified Data.Set as Set

> import Prelude hiding (length, foldr1, foldr, map, init)

We need to check 3 things:

* Lists have same size
* Lists have same elements
* Elements in the right order

Lets start with the _same size_ constraint:

> {-@ sort :: Ord a => xs:List a -> ListN a {length xs} @-}
> sort Emp = Emp
> sort (x ::: xs) = insert x (sort xs)

> {-@ insert :: Ord a => a -> xs:List a -> ListN a {length xs + 1} @-}
> insert :: Ord a => a -> List a -> List a
> insert x Emp        = x ::: Emp
> insert x (y ::: ys)
>   | x <= y          = x ::: (y ::: ys)
>   | otherwise       = y ::: insert x ys

Now, lets ensure that a sorted list have the same elements.
SMT solvers reason about sets. Hence, we can write set-valued measures.

> {-@ measure elems @-}
> elems :: Ord a => List a -> Set a
> elems Emp = Set.empty
> elems (x ::: xs) = addElem x xs

> {-@ inline addElem @-}
> addElem :: Ord a => a -> List a -> Set a
> addElem x xs = Set.union (Set.singleton x) (elems xs)

`inline` lets us reuse Haskell terms in refinements.
