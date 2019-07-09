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

* [the book](https://github.com/ucsd-progsys/liquidhaskell-tutorial/blob/master/pdf/programming-with-refinement-types.pdf)
* [the talk](https://www.youtube.com/watch?v=vQrutfPAERQ)
* [with Nix](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/NIX.md)
* [with Emacs](https://github.com/ucsd-progsys/liquid-types.el)


# Notes

**This is a Literal Haskell file!** So feel free to play around
with the examples!

There is a Liquid Haskell [integration
package](https://github.com/spinda/liquidhaskell-cabal) for
Cabal and Stack. See the
[liquidhaskell-cabal-demo](https://github.com/spinda/liquidhaskell-cabal-demo)
for an example project setup. This project is another example of
using `liquidhaskell-cabal`.
Refinement Types = `Types` + `Predicates`.

``` haskell literate
module A1 where
```

``` haskell literate
{-@ LIQUID "--no-termination" @-}
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
  calc
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

**Implication** and **if-and-only-if** operators.

``` haskell literate
module B1 where
```

`==>` and `<=>` are special operators.

`==>` is the **implication** operator, equivalent the following Haskell
function:

``` haskell literate
infixr 7 ==>
{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
(==>) :: Bool -> Bool -> Bool
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False
```

`<=>` is the **if-and-only-if** operator, which is equivalent to the
Haskell function:

``` haskell literate
infixr 7 <=>
{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
(<=>) :: Bool -> Bool -> Bool
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False
```

An **environment** is a mapping from variables to their Haskell types.
For example, let `G` be an environment:

``` haskell
x :: Int
y :: Int
z :: Int
```

Satisfaction:

A **predicate** is SATISFIABLE in a env `G` if *there exists* an
**assignment** in `G` that makes the **predicate** evaluate to `True`.

``` haskell
x + y == z
```

Validity:

A **predicate** is VALID in an env `G` if *every* **assignment** make a
**predicate** evalue to `True`.

``` haskell
x < 10 || x == 10 || x > 10
```

Verification conditions:

LH checks the program in roughly 2 steps:

1.  Combines code and types down to a set of *Verification Conditions
    (VC)* which are **predicates** that are valid *only if* the program
    satisfies a given property which are **predicates** that are valid
    *only if* the program satisfies a given property.

2.  Quries the **SMT solver** (e.g. `Z3`) to determine whether these
    **VC**’s are valid.

Examples (Prepositions).

Here `TRUE` is a *refined type* for `Bool` valued expressions that
*always* evaluate to `True`:

``` haskell literate
{-@ type TRUE = {v:Bool | v} @-}
```

Same with `FALSE`:

``` haskell literate
{-@ type FALSE = {v:Bool | not v} @-}
```

Lets see some examples:

Valid:

``` haskell literate
{-@ ex0 :: TRUE @-}
ex0 :: Bool
ex0 = True
```

Invalid:

``` haskell
{-@ ex0' :: TRUE @-}
ex0' :: Bool
ex0' = False
```

Valid:

``` haskell literate
{-@ ex1 :: Bool -> TRUE @-}
ex1 :: Bool -> Bool
ex1 b = b || not b
```

Valid as well:

``` haskell literate
{-@ ex2 :: Bool -> FALSE @-}
ex2 :: Bool -> Bool
ex2 b = b && not b
```

Examples with `==>` operator.

Read `p ==> q` as: \_if `p` is `true` then `q` must also be `true`.

``` haskell literate
{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 :: Bool -> Bool -> Bool
ex3 a b = (a && b) ==> a
```

``` haskell literate
{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 :: Bool -> Bool -> Bool
ex4 a b = (a && b) ==> b
```

Ex 2.1:

``` haskell literate
{-@ ex3' :: Bool -> Bool -> TRUE @-}
ex3' :: Bool -> Bool -> Bool
ex3' a _ = (a || a) ==> a
```

Modus ponens:

``` haskell literate
{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 :: Bool -> Bool -> Bool
ex6 a b = (a && (a ==> b)) ==> b
```

``` haskell literate
{-@ ex7 :: Bool -> Bool -> TRUE @-}
ex7 :: Bool -> Bool -> Bool
ex7 a b = a ==> (a ==> b) ==> b
```

De Morgan’s laws:

``` haskell literate
{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 :: Bool -> Bool -> Bool
exDeMorgan1 a b = not (a || b) <=> (not a && not b)
```

``` haskell literate
{-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
exDeMorgan2 :: Bool -> Bool -> Bool
exDeMorgan2 a b = not (a && b) <=> (not a || not b)
```

Examples: Arithmetic

Ok:

``` haskell literate
{-@ ax0 :: TRUE @-}
ax0 :: Bool
ax0 = 1 + 1 == 2
```

Not ok:

``` haskell
{-@ ax0' :: TRUE @-}
ax0' :: Bool
ax0' = 1 + 1 == 3
```

Via the laws of arithmetic, it is equivalent to `0 < 1`, which is `True`
independent of the value of `x`.

``` haskell literate
{-@ ax1 :: Int -> TRUE @-}
ax1 :: Int -> Bool
ax1 x = x < x + 1
```

We can combine arithmetic and prepositional operators:

``` haskell literate
{-@ ax2 :: Int -> TRUE @-}
ax2 :: Int -> Bool
ax2 x = (x < 0) ==> (0 <= 0 - x)
```

``` haskell literate
{-@ ax3 :: Int -> Int -> TRUE @-}
ax3 :: Int -> Int -> Bool
ax3 x y = (0 <= x) ==> (0 <= y) ==> (0 <= x + y)
```

``` haskell literate
{-@ ax4 :: Int -> Int -> TRUE @-}
ax4 :: Int -> Int -> Bool
ax4 x y = (x == y - 1) ==> (x + 2 == y + 1)
```

``` haskell literate
{-@ ax5 :: Int -> Int -> Int -> TRUE @-}
ax5 :: Int -> Int -> Int -> Bool
ax5 x y z =   (x <= 0 && x >= 0)
          ==> (y == x + z)
          ==> (y == z)
```

Ex 2.3:

``` haskell literate
{-@ ax6 :: Int -> Int -> TRUE @-}
ax6 :: Int -> Int -> Bool
ax6 x y = False ==> (x <= x + y)
```

Examples: Uninterpreted function

SMT solver doesn’t know how functions are defined. It only knows the
*axiom of conguence*: any function `f` returns equal outputs when
invoked on equal inputs.

Lets define an uninterpreted function from `Int` to `Int`:

``` haskell literate
{-@ measure f :: Int -> Int @-}
```

We test the axiom by checking the following predicate:

``` haskell
{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)
```

Whatever.

``` haskell literate
module B2 where
```
