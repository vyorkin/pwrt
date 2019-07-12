

Numeric measures.

Wholemeal programming.

> {-# LANGUAGE ScopedTypeVariables #-}
> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--short-names"    @-}

> module B5 where

> import Prelude hiding (map, reverse, zipWith, zip)
> import qualified Prelude as P
> import A1 (die)

We'll need some stuff from the previous chapters:

> {-@ type TRUE = {v:Bool | v} @-}

We can use **measures** to specify dimensions and create a
dimension-aware API for lists which can be used to implement
wholemeal dimension-safe APIs.

> data Vector a = V
>   { vDim :: Int
>   , vEls :: [a]
>   }
>   deriving (Eq)

> data Matrix a = M
>   { mRow :: Int
>   , mCol :: Int
>   , mEls :: Vector (Vector a)
>   }
>   deriving (Eq)

> dotProd :: Num a => Vector a -> Vector a -> a
> dotProd vx vy = sum (prod xs ys)
>   where
>     prod = P.zipWith (*)
>     xs   = vEls vx
>     ys   = vEls vy

> matProd :: Num a => Matrix a -> Matrix a -> Matrix a
> matProd (M rx _ xs) (M _ cy ys) = M rx cy els
>   where
>     els = for xs $ \xi ->
>             for ys $ \yj ->
>               dotProd xi yj

> for :: Vector a -> (a -> b) -> Vector b
> for (V n xs) f = V n (f <$> xs)

We need a way to represent the _dimensions_.
**Measures** are ideal for this task, so lets write a
measure to describe the length of a list:

> {-@ measure size @-}
> size :: [a] -> Int
> size []     = 0
> size (_:rs) = 1 + size rs

Just a reminder: a **measure** is an _inductively defined
 function_ with a single equative per data-constructor.

As with _refined data definitions_,
the measures are translated into smth like this:

< data [a] where
<   []  :: { v:[a] | size v = 0 }
<   (:) :: a -> xs:[a] -> { v:[a] | size v = 1 + size xs }

Multiple measures may be defined for
the same data type, for example:

> {-@ measure notEmpty @-}
> notEmpty :: [a] -> Bool
> notEmpty []    = False
> notEmpty (_:_) = True

Different measures can be composed by _conjoining_ the refinements.
For example, lets compose `size` and `notEmpty` measures:

< data [a] where
<   []  :: { v:[a] | not (notEmpty v) size v = 0 }
<   (:) :: a
<       -> xs:[a]
<       -> { v:[a] | notEmpty v && size v = 1 + size xs }

**Measure**'s decouples _property_ from _structure_, which
enabled the use of the same structure for many different purposes.

To make signatures symmetric:

> type List a = [a]

> {-@ type ListN a N = { v:List a | size v == N } @-}
> {-@ type ListX a X = ListN a { size X } @-}

Ex 7.1 (Map)

> {-@ map :: (a -> b) -> xs:List a -> ListX b xs @-}
> map :: (a -> b) -> List a -> List b
> map f (x:xs) = f x : map f xs
> map _ [] = []

> {-@ prop_map :: forall a. xs:List a -> TRUE @-}
> prop_map :: forall a. List a -> Bool
> prop_map xs = size ys == size xs
>   where
>     {-@ ys :: ListX a xs @-}
>     ys :: List a
>     ys = map id xs

Ex 7.2 (Reverse)

> {-@ reverse :: xs:List a -> ListX a xs @-}
> reverse :: List a -> List a
> reverse = go []
>   where
>     {-@ go :: ys:List a -> xs:List a -> ListN a {size xs + size ys} @-}
>     go :: List a -> List a -> List a
>     go acc []     = acc
>     go acc (x:xs) = go (x:acc) xs

> {-@ invariant {v:[a] | 0 <= size v} @-}

> {-@ zipWith :: (a -> b -> c) -> xs:List a -> ListX b xs -> ListX c xs @-}
> zipWith :: (a -> b -> c) -> List a -> List b -> List c
> zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
> zipWith _ [] []         = []
> zipWith _ _ _           = die "impossible"

Unsafe zip:

> {-@ zip :: as:[a] -> bs:[b] -> { v:[(a, b)] | Tinier v as bs } @-}
> zip :: [a] -> [b] -> [(a, b)]
> zip (a:as) (b:bs) = (a, b) : zip as bs
> zip [] _ = []
> zip _ [] = []

> {-@ predicate Tinier V X Y = Min (size V) (size X) (size Y) @-}
> {-@ predicate Min V X Y = (if X < Y then V == X else V == Y) @-}

Ex 7.3 (Zip unless empty)

TODO: How to draw an owl

< {-@
< zipOrNull
<   :: xs:List a
<   -> ys:List b
<    -> ListX (a, b) xs @-}
< zipOrNull :: [a] -> [b] -> [(a, b)]
< zipOrNull [] _  = []
< zipOrNull _ []  = []
< zipOrNull xs ys = zipWith (,) xs ys

< {-@ test1 :: { v:_ | size v = 2 } @-}
< test1 :: [(Int, Bool)]
< test1 = zipOrNull [0, 1] [True, False]
