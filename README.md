# pwrt

## Synopsis

Some notes, quotes & examples that I take while reading the
Programming with Refinement Types book.

## Setup

You need to install `z3 4.7.1` for now (They just made some
changes that makes 4.8 incompatible). Also, use `liquidhaskell`
from the `develop` branch.

Here is my NixOS config for `LH`:

* https://github.com/vyorkin/nixos-config/blob/740e30defff098ef5deabcae9038ead4d967575d/cfgs/development/proof-assistants.nix#L14
* https://github.com/vyorkin/nixos-config/blob/740e30defff098ef5deabcae9038ead4d967575d/cfgs/development/haskell/packages/default.nix#L9

My Emacs config for `LH`:

https://github.com/vyorkin/emacs.d#liquid-types

## Links

* https://www.youtube.com/watch?v=vQrutfPAERQ
* https://github.com/ucsd-progsys/liquidhaskell/blob/develop/NIX.md
* https://github.com/ucsd-progsys/liquid-types.el


# Notes

**This is a Literal Haskell file!** So feel free to play around
with the examples!

There is a Liquid Haskell [integration
package](https://github.com/spinda/liquidhaskell-cabal) for
Cabal and Stack. See the
[liquidhaskell-cabal-demo](https://github.com/spinda/liquidhaskell-cabal-demo)
for an example project setup.

This project is another example of using `liquidhaskell-cabal`.
Refinement Types = `Types` + `Predicates`.

``` haskell literate
module A1 where
```

Base types, type variables:

``` haskell
b := Int | Bool | ... | a, b, c
```

Refined base or refined function:

``` haskell
t := { x:b | p } | x:t -> t
```

Where `p` is a predicate in decidable logic:

``` haskell
p := e          -- atom
  | e1 == e2    -- equality
  | e1 <  e2    -- ordering
  | (p && p)    -- and
  | (p || p)    -- or
  | (not p)     -- negation
```

Where `e` is an expression:

``` haskell
e := x, y, z,...    -- variable
   | 0, 1, 2,...    -- constant
   | (e + e)        -- addition
   | (e - e)        -- subtraction
   | (c * e)        -- linear multiplication
   | (f e1 ... en)  -- uninterpreted function
```

Ok, lets try something\!

We use `{-@ ... @-}` to add refinement type annotations:

``` haskell
{-@ type Zero = {v:Int | v = 0} @-}
{-@ zero :: Zero @-}
zero :: Int
zero = 0
```

Natural numbers:

``` haskell literate
{-@ type Nat = {v:Int | 0 <= v} @-}
{-@ nats :: [Nat] @-}
nats :: [Int]
nats = [0, 1, 2]
```

Positive integers:

``` haskell literate
{-@ type Pos = {v:Int | 1 <= v} @-}
```

``` haskell literate
{-@ pos :: [Pos] @-}
pos :: [Int]
pos = [1, 2, 3]
```

Predicate Subtyping:

``` haskell
{-@ z :: Zero @-}
z :: Int
z = 0
```

Because `z :: Zero <: Nat`:

``` haskell
{-@ z' :: Nat @-}
z' :: Int
z' = z
```

Contracts (function types):

If the program type checks it means that `impossible` is never called at
runtime.

``` haskell literate
{-@ impossible :: {v:_ | false} -> a @-}
impossible :: [Char] -> a
impossible msg = error msg
```

Pre-conditions:

The next example won’t typecheck:

``` haskell
{-@ safeDiv :: Int -> Int -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n
```

But this one will:

``` haskell literate
{-@ type NonZero = {v:Int | v /= 0} @-}
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv x n = x `div` n
```

Verifying user input:

``` haskell literate
calc :: IO ()
calc = do
  putStrLn "Enter numerator"
  n <- readLn
  putStrLn "Enter denominator"
  d <- readLn
  if d == 0
    then putStrLn "Blya"
    else putStrLn ("Result = " ++ show (safeDiv n d))
  -- calc
```

Another way could be:

``` haskell literate
{-@ foo :: Int -> Maybe {v:Int | v /= 0} @-}
foo :: Int -> Maybe Int
foo 0 = Nothing
foo n = Just n
```

``` haskell
...
case foo d of
Nothing -> putStrLn "Blya"
Just n  -> ...
...
```

Won’t typecheck (`n` could be `0`)

``` haskell literate
avg :: [Int] -> Int
avg xs = safeDiv total n
  where
    total = sum xs
    n = size xs
```

We could specify **post-condition** as **output-type**:

``` haskell literate
{-@ size :: [a] -> Pos @-}
size :: [a] -> Int
size []     = 1
size (_:xs) = 1 + size xs
```

The next section is about data types.

``` haskell literate
{-# LANGUAGE ScopedTypeVariables #-}
```

``` haskell literate
module A2 where
```

``` haskell literate
import A1
import Prelude hiding (length, foldr1, foldr, map, init)
```

``` haskell literate
data List a
  = Emp
  | a ::: List a
```

Measures:

``` haskell literate
{-@ measure length @-}
length :: List a -> Int
length Emp = 0
length (_ ::: xs) = 1 + length xs
```

And now LH knows the following properties about our `List a`:

``` haskell
data List a where
  Emp   :: {v:List a | length v = 0}
  (:::) :: x:a -> xs:List a
        -> {v:List a | length v = 1 + length xs}
```

Lets make a type alias for a non-empty `List`:

``` haskell literate
{-@ type ListNE a = {v:List a | length v > 0} @-}
```

And now `head` and `tail` functions are not *partial* anymore:

``` haskell literate
{-@ head :: ListNE a -> a @-}
head (x ::: _) = x
```

``` haskell literate
{-@ tail :: ListNE a -> List a @-}
tail (_ ::: xs) = xs
```

*Fold* `f` over list initially using *first* element:

``` haskell literate
{-@ foldr1 :: (a -> a -> a) -> ListNE a -> a @-}
foldr1 :: (a -> a -> a) -> List a -> a
foldr1 f (x ::: xs) = foldr f x xs
foldr1 _ _          = impossible "foldr1"
```

``` haskell literate
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ acc Emp = acc
foldr f acc (x ::: xs) = f x (foldr f acc xs)
```

Another average:

``` haskell literate
{-@ average' :: ListNE Int -> Int @-}
average' :: List Int -> Int
average' xs = total `div` n
  where
    total = foldr1 (+) xs
    n = length xs
```

We can refine data types and make illegal states unrepresentable. For
example, lets make sure that every year has exactly 12 months.

``` haskell literate
data Year a = Year (List a)
```

``` haskell literate
{-@ data Year a = Year (ListN a 12) @-}
```

We need a type for lists of a given size.

``` haskell literate
{-@ type ListN a N = {v: List a | length v == N } @-}
```

Now, this won’t typecheck:

``` haskell
badYear :: Year Int
badYear = Year (1 ::: Emp)
```

Mapping:

``` haskell literate
{-@ map :: (a -> b) -> xs:List a -> ys:ListN b {length xs} @-}
map :: (a -> b) -> List a -> List b
map _ Emp = Emp
map f (x ::: xs) = f x ::: map f xs
```

Lets write a function to calculate an average temperature of the year:

``` haskell literate
data Weather = W { temp :: Int, rain :: Int }
```

``` haskell literate
tempAverage :: Year Weather -> Int
tempAverage (Year ms) = average' months
  where
    months = map temp ms
```

Another example:

``` haskell literate
{-@ init :: (Int -> a) -> n:Nat -> ListN a n @-}
init :: (Int -> a) -> Int -> List a
init _ 0 = Emp
init f n = f n ::: init f (n - 1)
```

``` haskell literate
sanDiegoTemp :: Year Int
sanDiegoTemp = Year (init (const 72) 12)
```

It seems that the problem is in the following condition `VV < i` , but I
don’t understand where this condition comes from. Asked in slack,
waiting for reply.

``` haskell
{-@ init' :: (Int -> a) -> n:Nat -> ListN a n @-}
init' :: forall a. (Int -> a) -> Int -> List a
init' f n = go 0
  where
    {-@ go :: i:_ -> ListN a {n - i} @-}
    go :: Int -> List a
    go i | i < n     = f i ::: go (i + 1)
         | otherwise = Emp
```

``` haskell
sanDiegoTemp' :: Year Int
sanDiegoTemp' = Year (init' (const 72) 12)
```

Case study: **Insertion Sort**.

``` haskell literate
{-# LANGUAGE ScopedTypeVariables #-}
```

``` haskell literate
module A3 where
```

``` haskell literate
import A2
import Data.Set (Set)
import qualified Data.Set as Set
```

``` haskell literate
import Prelude hiding (length, foldr1, foldr, map, init)
```

We need to check 3 things:

  - Lists have same size
  - Lists have same elements
  - Elements in the right order

Lets start with the *same size* constraint:

``` haskell literate
{-@ sort :: Ord a => xs:List a -> ListN a {length xs} @-}
sort Emp = Emp
sort (x ::: xs) = insert x (sort xs)
```

``` haskell literate
{-@ insert :: Ord a => a -> xs:List a -> ListN a {length xs + 1} @-}
insert :: Ord a => a -> List a -> List a
insert x Emp        = x ::: Emp
insert x (y ::: ys)
  | x <= y          = x ::: (y ::: ys)
  | otherwise       = y ::: insert x ys
```

Now, lets ensure that a sorted list have the same elements. SMT solvers
reason about sets. Hence, we can write set-valued measures.

Fails with `Termination Error`, `no decreasing parameter`. Asked in
Slack, will come back to this later.

``` haskell
{-@ measure elems @-}
elems :: Ord a => List a -> Set a
elems Emp = Set.empty
elems (x ::: xs) = addElem x xs
```

``` haskell
{-@ inline addElem @-}
addElem :: Ord a => a -> List a -> Set a
addElem x xs = Set.union (Set.singleton x) (elems xs)
```

`inline` lets us reuse Haskell terms in refinements.
