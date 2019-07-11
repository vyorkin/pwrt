

Polymorphism.

> {-@ LIQUID "--short-names" @-}
> {-@ LIQUID "--no-termination"      @-}
> {-@ LIQUID "--scrape-used-imports" @-}

> module B2 where

> import A1 (abs)
> import Prelude hiding (length, abs)
> import Data.Vector hiding (head, foldl')
> import Data.List (foldl')

Array bounds verification:

> twoLangs :: Vector String
> twoLangs = fromList ["haskell", "javascript"]

We get a runtime exception with this:

< eeks :: [String]
< eeks = [ok, yup, nono]
<   where
<     ok   = twoLangs ! 0
<     yup  = twoLangs ! 1
<     nono = twoLangs ! 3

We can write specifications for imported modules --
either _in place_ or (better), in `.spec` files, which
could be reused across multiple modules.

We can write specifications for external modules inside
special `include` directories.

For example, for `Data.Vector` we'll need
`include/Data/Vector.spec` with the following contents:

< -- | Define the size
< measure vlen :: Vector a -> Int

< -- | Compute the size
< assume length :: x:Vector a -> {v:Int | v = vlen x}

< -- | Lookup at an index
< assume (!) :: x:Vector a -> {v:Nat | v < vlen x} -> a

To use this specification:

< liquid -i include/ foo.hs

LiquidHaskell ships with specifications for `Prelude`, `Data.List` nad `Data.Vector`
which it includes by default.

**Measures** - define _properties_ of Haskell data values that
are used for specification and verification.

**Assumes** - _specify_ types describing semantics of functions that we cannot verify
because we don't have the code for them.

**Alises** - _abbreviations_ for commonly occurring types, e.g.:

> {-@ type VectorN a N = {v:Vector a | vlen v == N} @-}

> {-@ twoLangs :: VectorN String 2 @-}

or

> {-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

then we can

< (!) :: x:Vector a -> Btwn 0 (vlen x) -> a

Lets try something.

What if `vec` had _no_ elements?
A formal verifier doesn't make _off by one_ errors:

< head :: Vector a -> a
< head vec = vec ! 0

Lets fix that:

> {-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}

We've specified `NEVector` is a _non-empty_ vector,
so now our new `head'` verifies:

> {-@ head' :: NEVector a -> a @-}
> head' :: Vector a -> a
> head' vec = vec ! 0

Ex 4.1 (Vector head)

> head'' :: Vector a -> Maybe a
> head'' vec = vec !? 0

Ex 4.2 (Unsafe lookup)

> {-@ type GTVector a N = {v:Vector a | N < vlen v} @-}

> {-@ unsafeLookup :: ix:Nat -> GTVector a ix -> a @-}
> unsafeLookup :: Int -> Vector a -> a
> unsafeLookup ix vec = vec ! ix

Ex 4.3 (Safe lookup)

> {-@ safeLookup :: Vector a -> Int -> Maybe a @-}
> safeLookup :: Vector a -> Int -> Maybe a
> safeLookup x i
>   | ok = Just (x ! i)
>   | otherwise = Nothing
>   where
>     ok = 0 < i && i < length x

Inference.

LH verifies the `vectorSum` function below (safety of `vec ! i`)
because LH is able to automatically infer:

< go :: Int -> {v:Int | 0 <= v && v <= sz} -> Int

> vectorSum :: Vector Int -> Int
> vectorSum vec = go 0 0
>   where
>     go :: Int -> Int -> Int
>     go acc i
>       | i < sz    = go (acc + (vec ! i)) (i + 1)
>       | otherwise = acc
>     sz = length vec

Ex 4.6 (Why `v <= sz` and not `v < sz`?)

Because when `i < sz` we call `go acc (i + 1)` and
`i + 1 <= sz` in this case.

Ex 4.5 (Absolute sum)

> {-@ absoluteSum :: Vector Int -> Nat @-}
> absoluteSum :: Vector Int -> Int
> absoluteSum vec = go 0 0
>   where
>     go acc i
>       | i < length vec = go (acc + abs (vec ! i)) (i + 1)
>       | otherwise      = acc

High-order functions.

> {-@ loop :: lo:Nat -> hi:{Nat | lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a @-}
> loop :: Int -> Int -> a -> (Int -> a -> a) -> a
> loop lo hi base f = go base lo
>  where
>    go acc i
>      | i < hi    = go (f i acc) (i + 1)
>      | otherwise = acc

LH finds that:

< loop
<   :: lo:Nat
<   -> hi:{Nat | lo <= hi}
<   -> a
<   -> (Btwn lo hi -> a -> a)
<   -> a

TODO: Have no idea what's wrong here

< vectorSum' :: Vector Int -> Int
< vectorSum' vec = loop 0 n 0 body
<   where
<     body i acc = acc + (vec ! i)
<     n = length vec

Ex 4.7 (High-order loops)

> {-@ absoluteSum' :: Vector Int -> Nat @-}
> absoluteSum' :: Vector Int -> Int
> absoluteSum' vec = loop 0 (length vec) 0 body
>   where
>     {-@ body :: Int -> _ -> Nat @-}
>     body :: Int -> Int -> Int
>     body i acc = acc + abs (vec ! i)

Ex 4.8

> {-@
> dotProduct
>   :: x:Vector Int
>   -> {y:Vector Int | vlen x == vlen y}
>   -> Int
> @-}
> dotProduct :: Vector Int -> Vector Int -> Int
> dotProduct x y = loop 0 (length x) 0 body
>   where
>     body :: Int -> Int -> Int
>     body i acc = acc + (x ! i) * (y ! i)

Refinements and Polymorphism.

Lets make an alias for a sparse vectors and
write a function to compute sparse product.

> {-@ type SparseN a N = [(Btwn 0 N, a)] @-}

Since we know that all indexes are with the bounds of the source
array the following function verifies:

> {-@ sparseProduct :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
> sparseProduct :: Num a => Vector a -> [(Int, a)] -> a
> sparseProduct x y = go 0 y
>   where
>     go acc [] = acc
>     go acc ((i, v):ys) = go (acc + (x ! i) * v) ys

Another way to represend the _sparse product_ is using `fold`.
For example:

< foldl' :: (a -> b -> a) -> a -> [b] -> a

GHC infers that:

< foldl' :: (a -> (Int, a)) -> a -> [(Int, a)] -> a

LH infers that:

< b :: (Btwn 0 (vlen x), a)

> {-@ sparseProduct' :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
> sparseProduct' :: Num a => Vector a -> [(Int, a)] -> a
> sparseProduct' x y = foldl' body 0 y
>   where
>     body sum (i, v) = sum + (x ! i) * v
