

Lifting functions to Measures.

> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--short-names"    @-}

> module B4 where
> import Prelude hiding (head, tail, null, sum, foldl1)
> import qualified Prelude as P
> import A1 (safeDiv, die)

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
>     total = P.sum xs
>     elems = size xs

Ex 6.1 (Average, Maybe)

> average' :: [Int] -> Maybe Int
> average' xs
>   | elems > 0 = Just $ (P.sum xs) `safeDiv` elems
>   | otherwise = Nothing
>   where
>     elems = size xs

Ex 6.2 (Debugging specificatins)

These two examples below are rejected because
the `xs` in `(_:xs)` could be empty:

< {-@ size1 :: xs:NEList a -> Pos @-}
< size1 :: [a] -> Int
< size1 [] = 0
< size1 (_:xs) = 1 + size1 xs

< {-@ size2 :: xs:[a] -> { v:Int | notEmpty xs => v > 0 } @-}
< size2 :: [a] -> Int
< size2 [] = 0
< size2 (_:xs) = 1 + size2 xs

Since we have `NEList` we can use it to type the `head` and
`tail` functions:

> {-@ head :: NEList a -> a @-}
> head :: [a] -> a
> head (x:_) = x
> head []    = die "fear not"

> {-@ tail :: NEList a -> [a] @-}
> tail :: [a] -> [a]
> tail (_:xs) = xs
> tail []    = die "fear not"

LH uses the precondition to deduce that
the second equations are _dead code_.

Ex 6.3 (Safe head)

> safeHead :: [a] -> Maybe a
> safeHead xs
>   | null xs   = Nothing
>   | otherwise = Just $ head xs

> {-@ null :: xs:[a] -> {v:Bool | v <=> not notEmpty xs } @-}
> null :: [a] -> Bool
> null []    = True
> null (_:_) = False

Groups.

Lets write a function that chunks sequences into
non-empty groups of equal elements:

> {-@ groupEq :: Eq a => [a] -> [NEList a] @-}
> groupEq :: Ord a => [a] -> [[a]]
> groupEq []     = []
> groupEq (x:xs) = (x:ys) : groupEq zs
>   where
>     (ys, zs) = span (x ==) xs

Eliminate stuttering:

> eliminateStutter :: String -> String
> eliminateStutter = map head . groupEq

< λ> eliminateStutter "ssstringssss liiiiiike thisss"
< "strings like this"

> {-@ foldl1 :: (a -> a -> a) -> NEList a -> a @-}
> foldl1 :: (a -> a -> a) -> [a] -> a
> foldl1 f (x:xs) = foldl f x xs
> foldl1 _ [] = die "foldl1"

Sum of a non-empty list of `Num a`:

> {-@ sum :: Num a => NEList a -> a @-}
> sum :: Num a => [a] -> a
> sum [] = die "sum"
> sum xs = foldl1 (+) xs

> sumOk :: Int
> sumOk = sum [1, 2, 3]

< sumBad :: Int
< sumBad = sum []

< sumBad' :: Int
< sumBad' = sum [1..3]

Ex 6.4 (Weighted average)

> {-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
> wtAverage :: [(Int, Int)] -> Int
> wtAverage wxs = totElems `safeDiv` totWeight
>   where
>     elems     = map' (uncurry (*)) wxs
>     weights   = map' fst wxs
>     totElems  = sum' elems
>     totWeight = sum' weights

> {-@ sum' :: NEList Pos -> Pos @-}
> sum' :: [Int] -> Int
> sum' [] = die "sum"
> sum' xs = foldl1 (+) xs

> {-@ map' :: (a -> b) -> NEList a -> NEList b @-}
> map' :: (a -> b) -> [a] -> [b]
> map' _ []     = die "impossible"
> map' f (x:[]) = [f x]
> map' f (x:xs) = (f x) : map' f xs

Ex 6.5 (Mitchell's risers)

> {-@ risers :: Ord a => NEList a -> NEList [a] @-}
> risers :: (Ord a) => [a] -> [[a]]
> risers []  = die "impossible"
> risers [x] = [[x]]
> risers (x:y:etc)
>   | x <= y    = (x:s):ss
>   | otherwise = [x]:(s:ss)
>   where
>     (s, ss) = safeSplit $ risers (y:etc)

> {-@ safeSplit :: NEList a -> (a, [a]) @-}
> safeSplit :: [a] -> (a, [a])
> safeSplit (x:xs) = (x, xs)
> safeSplit _ = die "go forth and die"
