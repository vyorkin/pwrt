

Numeric measures.

Wholemeal programming.

> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--short-names"    @-}

> module B5 where
> import Prelude

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
>     prod = zipWith (*)
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
