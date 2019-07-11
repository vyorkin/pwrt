

Refined Datatypes.

> {-@ LIQUID "--short-names" @-}
> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--no-total" @-}

> module B3 where

> import Prelude hiding (abs, length, min)
> import Data.Vector hiding (singleton, foldl', foldr, fromList, (++), all)
> import Data.Maybe (fromJust)

Sparse vectors revisited.

> data Sparse a = SP
>   { spDim :: Int
>   , spElems :: [(Int, a)]
>   }

* `spDim` should be positive number
* every index in `spElems` should be `0 <= i < spDim`

> {-@
> data Sparse a = SP
>   { spDim :: Nat
>   , spElems :: [(Btwn 0 spDim, a)]
>   }
> @-}

> {-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

Now `SP` works like a _smart_ constructor!

> okSP :: Sparse String
> okSP = SP 5 [ (0, "cat")
>             , (3, "dog")
>             ]

< badSP :: Sparse String
< badSP = SP 5 [ (0, "cat")
<              , (6, "dog")
<              ]

Field measures.

Lets write an alias for sparse vectors of size `N`.

> {-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

Now we can write our `dotProd` function like this:

> {-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
> dotProd :: Vector Int -> Sparse Int -> Int
> dotProd x (SP _ y) = go 0 y
>   where
>     go acc []          = acc
>     go acc ((i, v):ys) = go (acc + (x ! i) * v) ys

And `fold`-based implementation:

Ex 5.1 (Sanitization)

> {-@ fromList :: n:Nat -> [(Btwn 0 n, _)] -> Maybe (SparseN _ n) @-}
> fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
> fromList dim elems
>   | all (< dim) (fst <$> elems) = Just $ SP dim elems
>   | otherwise = Nothing

> {-@ test1 :: SparseN String 3 @-}
> test1 :: Sparse String
> test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]

Ex 5.2 (Addition)

> {-@ plus :: SparseN a 3 -> SparseN a 3 -> SparseN a 3 @-}
> plus :: Sparse a -> Sparse a -> Sparse a
> plus v1 v2 = SP (spDim v1) (spElems v1 ++ spElems v2)

But I think the goal is to make a
general function that can work for any dimension.

> {-@ test2 :: SparseN Int 3 @-}
> test2 :: Sparse Int
> test2 = plus vec1 vec2
>   where
>     vec1 = SP 3 [(0, 12), (2, 9)]
>     vec2 = SP 3 [(0, 8),  (1, 100)]

Ordered lists.

> data IncList a
>   = Emp
>   | (:<) { hd :: a, tl :: IncList a }

> infixr 9 :<

We can specify that the elements are in order by
refining _every_ element in `tl` to be _greater than_ `hd`:

> {-@
> data IncList a =
>     Emp
>   | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} }
> @-}

> okList :: IncList Int
> okList = 1 :< 2 :< 3 :< Emp

< badList :: IncList Int
< badList = 2 :< 1 :< 3 :< Emp

Insertion sort.

> insertSort :: Ord a => [a] -> IncList a
> insertSort []     = Emp
> insertSort (x:xs) = insert x (insertSort xs)

> insert :: Ord a => a -> IncList a -> IncList a
> insert y Emp = y :< Emp
> insert y (x :< xs)
>   | y <= x = y :< x :< xs
>   | otherwise = x :< insert y xs

Ex 5.3

> insertSort' :: Ord a => [a] -> IncList a
> insertSort' = foldr insert Emp

Merge sort.

> split :: [a] -> ([a], [a])
> split (x:y:zs) =
>   let (xs, ys) = split zs
>   in (x:xs, y:ys)
> split xs = (xs, [])

Sometimes I get errors like http://ix.io/1N99 which really confuse me.

This is a “totality” error — it means your function/case
expression is missing a case and so LH cannot prove that case
is dead code and hence gives that error (e.g. the head or tail
function which is not defined on []). This feature was added
after the tutorial and the LH authors made totality on by
default. It can be switched off with `{-@ LIQUID “—no-total” @-}`.
Or of course it is better to implement the missing case.

We should however add to the error the missing patterns...

One way to get them right now is load the file in ghci with the
`-fwarn-incomplete-patterns` flag.

> merge :: Ord a => IncList a -> IncList a -> IncList a
> merge Emp ys = ys
> merge xs Emp = xs
> merge (x :< xs) (y :< ys)
>   | x <= y    = x :< merge xs (y :< ys)
>   | otherwise = y :< merge (x :< xs) ys

> mergeSort :: Ord a => [a] -> IncList a
> mergeSort []  = Emp
> mergeSort [x] = x :< Emp
> mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
>   where
>     (ys, zs) = split xs

Ex 5.4 (QuickSort)

> quickSort :: Ord a => [a] -> IncList a
> quickSort [] = Emp
> quickSort (x:xs) = append x lessers greaters
>   where
>     lessers  = quickSort [y | y <- xs, y < x]
>     greaters = quickSort [z | z <- xs, z >= x]

We need to ensure that `append` has a valid specification:

> {-@
> append
>   :: x:a
>   -> IncList {v:a | v < x}
>   -> IncList {v:a | v >= x}
>   -> IncList a
> @-}
> append :: Ord a => a -> IncList a -> IncList a -> IncList a
> append z Emp ys       = z :< ys
> append z (x :< xs) ys = x :< (append z xs ys)

Ordered trees.

> data BST a
>   = Leaf
>   | Node { root  :: a
>          , left  :: BST a
>          , right :: BST a
>          }

> okBST :: BST Int
> okBST =
>   Node 6
>     ( Node 2
>       (Node 1 Leaf Leaf)
>       (Node 4 Leaf Leaf)
>     )
>     ( Node 9
>       (Node 7 Leaf Leaf)
>       Leaf
>     )

> okBST' :: BST Int
> okBST' =
>   Node 5
>     ( Node 3
>       (Node 1 Leaf Leaf)
>       (Node 4 Leaf Leaf)
>     )
>     ( Node 8
>       (Node 7 Leaf Leaf)
>       Leaf
>     )

> {-@
> data BST a =
>     Leaf
>   | Node { root  :: a
>          , left  :: BSTL a root
>          , right :: BSTR a root
>          }
> @-}

> {-@ type BSTL a X = BST {v:a | v < X} @-}
> {-@ type BSTR a X = BST {v:a | v > X} @-}

< badBST :: BST Int
< badBST =
<   Node 66
<     ( Node 4
<       (Node 1 Leaf Leaf)
<       (Node 69 Leaf Leaf)
<     )
<     ( Node 99
<       (Node 77 Leaf Leaf)
<       Leaf
<     )

Ex 5.5 (Duplicates)

The answer is no. Each value is either `>` than other or `<`.
But `N > N` is impossible and `N < N` doesn't make any sense too.

Membership.

> mem :: Ord a => a -> BST a -> Bool
> mem _ Leaf = False
> mem k (Node k' l r)
>   | k == k'   = True
>   | k <  k'   = mem k l
>   | otherwise = mem k r

Singleton.

> one :: a -> BST a
> one x = Node x Leaf Leaf

Insertion.

> add :: Ord a => a -> BST a -> BST a
> add k' Leaf = one k'
> add k' t@(Node k l r)
>   | k' < k    = Node k (add k' l) r
>   | k  < k'   = Node k l (add k' r)
>   | otherwise = t

Minimum.

> data MinPair a = MP
>   { mEl :: a
>   , mRest :: BST a
>   }

> {-@
> data MinPair a = MP
>   { mEl :: a
>   , mRest :: BSTR a mEl
>   }
> @-}

Looks like the `delMin` example from page 55 needs an additional
restriction (that `BST a` isn't just a `Leaf`) + maybe something else.

As I can see right now, nothing prevents `BST a` from being a
`Leaf` So `delMin Leaf = die "impossible"` branch is possible
and verification fails for me with error http://ix.io/1O9r.

< {-@ delMin :: BST a -> MinPair a @-}
< delMin :: Ord a => BST a -> MinPair a
< delMin (Node k Leaf r) = MP k r
< delMin (Node k l r) =
<   let MP k' l' = delMin l
<   in MP k' (Node k l' r)
< delMin Leaf = die "impossible"

Ex 5.6 (Delete)

Depends on `delMin`.

Ex 5.7. (Safely deleting minimum)

Depends on `delMin`.

Ex 5.8 (BST sort).

TODO!
