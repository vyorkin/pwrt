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

**Refinement types** allows us to decorate types with *logical
predicates*, that contrain the set of values described by the type.

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

``` haskell literate
{-@ type Zero = {v:Int | v = 0} @-}
{-@ zero :: Zero @-}
zero :: Int
zero = 0
```

Predicate Subtyping:

``` haskell literate
{-@ type Nat   = {v:Int | 0 <= v}        @-}
{-@ type Even  = {v:Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v:Int | v < 100}       @-}
```

Natural numbers:

``` haskell literate
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

Zero:

``` haskell literate
{-@ z :: Zero @-}
z :: Int
z = 0
```

Because `z :: Zero <: Nat`:

``` haskell literate
{-@ z' :: Nat @-}
z' :: Int
z' = z
```

Also:

``` haskell literate
{-@ z'' :: Even @-}
z'' :: Int
z'' = z
```

And this one as well:

``` haskell literate
{-@ z''' :: Lt100 @-}
z''' :: Int
z''' = z
```

When we *erase* the *refinement* we get the standart Haskell types. For
example, the `Int` is equivalent to `{v:Int | true}` because any
standart Haskell type has the trivial refinement `true`.

Writing specifications and *typing dead code*.

Contracts (function types):

If the program type checks it means that `impossible` is never called at
runtime.

``` haskell literate
{-@ impossible :: {v:String | false} -> a @-}
impossible :: String -> a
impossible msg = error msg
```

``` haskell literate
{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die msg = impossible msg
```

For example, LH will *accept*:

``` haskell literate
cannonDie :: ()
cannonDie =
  if 1 + 1 == 3
  then die "horrible death"
  else ()
```

But will *reject*:

``` haskell
canDie :: ()
canDie =
  if 1 + 1 == 2
  then die "horrible death"
  else ()
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

Post-conditons.

We can specify a *post-condition* as *output-type*.

For example, lets refine the output type of the `abs` function to say
that it returns only non-negative values:

``` haskell literate
{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs n
  | 0 < n = n
  | otherwise = -n
```

Because SMT solver has built-in decision procedures for arithmetic.

Ex 3.1:

``` haskell literate
avg :: [Int] -> Int
avg xs = safeDiv total n
  where
    total = sum xs
    n = size xs
```

``` haskell literate
{-@ size :: [a] -> Pos @-}
size :: [a] -> Int
size []     = 1
size (_:xs) = 1 + size xs
```

Another way to solve the `calc` exercise is to define a function like:

``` haskell literate
{-@ nonZero :: Int -> Maybe {v:Int | v /= 0} @-}
nonZero :: Int -> Maybe Int
nonZero 0 = Nothing
nonZero n = Just n
```

``` haskell
...
case nonZero d of
  Nothing -> putStrLn "Blya"
  Just n  -> ...
...
```

Or

``` haskell literate
result :: Int -> Int -> String
result n d
  | isPositive d = "result = " ++ show (n `safeDiv` d)
  | otherwise    = "blya"
```

Ex 3.2:

``` haskell literate
{-@ isPositive :: x:_ -> {v:Bool | v <=> x > 0} @-}
isPositive :: (Ord a, Num a) => a -> Bool
isPositive = (> 0)
```

``` haskell literate
calc' :: IO ()
calc' = do
  putStrLn "n: "
  n <- readLn
  putStrLn "d: "
  d <- readLn
  putStrLn $ result n d
  calc
```

Ex 3.3: Assertions

``` haskell literate
{-@ lAssert :: {v:Bool | v} -> a -> a @-}
lAssert :: Bool -> a -> a
lAssert True x  = x
lAssert False _ = die "assertion failed!"
```

``` haskell literate
yes = lAssert (1 + 1 == 2) ()
```

``` haskell
no  = lAssert (1 + 1 == 3) ()
```

The next section is about data types.

``` haskell literate
{-# LANGUAGE ScopedTypeVariables #-}
```

``` haskell literate
module A2 where
```

``` haskell literate
import A1 (impossible)
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
{-@ LIQUID "--no-termination" @-}
```

``` haskell literate
module A3 where
```

``` haskell literate
import A1 (impossible)
import A2 (List(..), length)
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

``` haskell literate
{-@ measure elems @-}
elems :: Ord a => List a -> Set a
elems Emp = Set.empty
elems (x ::: xs) = addElem x xs
```

``` haskell literate
{-@ inline addElem @-}
addElem :: Ord a => a -> List a -> Set a
addElem x xs = Set.union (Set.singleton x) (elems xs)
```

`inline` lets us reuse Haskell terms in refinements.

**Implication** and **if-and-only-if** operators.

``` haskell literate
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--higherorder" @-}
```

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

``` haskell literate
{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)
```

I’m too stupid to figure out why this predicate is invalid.

``` haskell literate
{-@ fx1 :: (Int -> Int) -> Int -> TRUE @-}
fx1 :: (Int -> Int) -> Int -> Bool
fx1 f x =  (x == f (f (f x)))
       ==> (x == f (f (f (f x))))
       ==> (x == f x)
```

To get a taste:

``` haskell literate
{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs
```

Now we can verify the following predicate. The SMT doesn’t need to
evaluate the `size` function to proove it.

``` haskell literate
{-@ fx0 :: [a] -> [a] -> TRUE @-}
fx0 :: Eq a => [a] -> [a] -> Bool
fx0 xs ys = (xs == ys) ==> (size xs == size ys)
```

But

``` haskell
{-@ fx2 :: a -> [a] -> TRUE @-}
fx2 :: Eq a => a -> [a] -> Bool
fx2 x xs = 0 < size ys
  where
    ys = x : xs
```

But

``` haskell literate
{-@ fx2VC :: [a] -> [b] -> TRUE @-}
fx2VC :: [a] -> [b] -> Bool
fx2VC xs ys =   (0 <= size xs)
            ==> (size ys == 1 + size xs)
            ==> (0 < size ys)
```

Polymorphism.

``` haskell literate
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}
```

``` haskell literate
module B2 where
```

``` haskell literate
import A1 (abs)
import Prelude hiding (length, abs)
import Data.Vector hiding (head, foldl')
import Data.List (foldl')
```

Array bounds verification:

``` haskell literate
twoLangs :: Vector String
twoLangs = fromList ["haskell", "javascript"]
```

We get a runtime exception with this:

``` haskell
eeks :: [String]
eeks = [ok, yup, nono]
  where
    ok   = twoLangs ! 0
    yup  = twoLangs ! 1
    nono = twoLangs ! 3
```

We can write specifications for imported modules – either *in place* or
(better), in `.spec` files, which could be reused across multiple
modules.

We can write specifications for external modules inside special
`include` directories.

For example, for `Data.Vector` we’ll need `include/Data/Vector.spec`
with the following contents:

``` haskell
-- | Define the size
measure vlen :: Vector a -> Int
```

``` haskell
-- | Compute the size
assume length :: x:Vector a -> {v:Int | v = vlen x}
```

``` haskell
-- | Lookup at an index
assume (!) :: x:Vector a -> {v:Nat | v < vlen x} -> a
```

To use this specification:

``` haskell
liquid -i include/ foo.hs
```

LiquidHaskell ships with specifications for `Prelude`, `Data.List` nad
`Data.Vector` which it includes by default.

**Measures** - define *properties* of Haskell data values that are used
for specification and verification.

**Assumes** - *specify* types describing semantics of functions that we
cannot verify because we don’t have the code for them.

**Alises** - *abbreviations* for commonly occurring types, e.g.:

``` haskell literate
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
```

``` haskell literate
{-@ twoLangs :: VectorN String 2 @-}
```

or

``` haskell literate
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
```

then we can

``` haskell
(!) :: x:Vector a -> Btwn 0 (vlen x) -> a
```

Lets try something.

What if `vec` had *no* elements? A formal verifier doesn’t make *off by
one* errors:

``` haskell
head :: Vector a -> a
head vec = vec ! 0
```

Lets fix that:

``` haskell literate
{-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}
```

We’ve specified `NEVector` is a *non-empty* vector, so now our new
`head'` verifies:

``` haskell literate
{-@ head' :: NEVector a -> a @-}
head' :: Vector a -> a
head' vec = vec ! 0
```

Ex 4.1 (Vector head)

``` haskell literate
head'' :: Vector a -> Maybe a
head'' vec = vec !? 0
```

Ex 4.2 (Unsafe lookup)

``` haskell literate
{-@ type GTVector a N = {v:Vector a | N < vlen v} @-}
```

``` haskell literate
{-@ unsafeLookup :: ix:Nat -> GTVector a ix -> a @-}
unsafeLookup :: Int -> Vector a -> a
unsafeLookup ix vec = vec ! ix
```

Ex 4.3 (Safe lookup)

``` haskell literate
{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup :: Vector a -> Int -> Maybe a
safeLookup x i
  | ok = Just (x ! i)
  | otherwise = Nothing
  where
    ok = 0 < i && i < length x
```

Inference.

LH verifies the `vectorSum` function below (safety of `vec ! i`) because
LH is able to automatically infer:

``` haskell
go :: Int -> {v:Int | 0 <= v && v <= sz} -> Int
```

``` haskell literate
vectorSum :: Vector Int -> Int
vectorSum vec = go 0 0
  where
    go :: Int -> Int -> Int
    go acc i
      | i < sz    = go (acc + (vec ! i)) (i + 1)
      | otherwise = acc
    sz = length vec
```

Ex 4.6 (Why `v <= sz` and not `v < sz`?)

Because when `i < sz` we call `go acc (i + 1)` and `i + 1 <= sz` in this
case.

Ex 4.5 (Absolute sum)

``` haskell literate
{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum :: Vector Int -> Int
absoluteSum vec = go 0 0
  where
    go acc i
      | i < length vec = go (acc + abs (vec ! i)) (i + 1)
      | otherwise      = acc
```

High-order functions.

``` haskell literate
{-@ loop :: lo:Nat -> hi:{Nat | lo <= hi} -> a -> (Btwn lo hi -> a -> a) -> a @-}
loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go base lo
 where
   go acc i
     | i < hi    = go (f i acc) (i + 1)
     | otherwise = acc
```

LH finds that:

``` haskell
loop
  :: lo:Nat
  -> hi:{Nat | lo <= hi}
  -> a
  -> (Btwn lo hi -> a -> a)
  -> a
```

TODO: Have no idea what’s wrong here

``` haskell
vectorSum' :: Vector Int -> Int
vectorSum' vec = loop 0 n 0 body
  where
    body i acc = acc + (vec ! i)
    n = length vec
```

Ex 4.7 (High-order loops)

``` haskell literate
{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum' :: Vector Int -> Int
absoluteSum' vec = loop 0 (length vec) 0 body
  where
    {-@ body :: Int -> _ -> Nat @-}
    body :: Int -> Int -> Int
    body i acc = acc + abs (vec ! i)
```

Ex 4.8

``` haskell literate
{-@
dotProduct
  :: x:Vector Int
  -> {y:Vector Int | vlen x == vlen y}
  -> Int
@-}
dotProduct :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 (length x) 0 body
  where
    body :: Int -> Int -> Int
    body i acc = acc + (x ! i) * (y ! i)
```

Refinements and Polymorphism.

Lets make an alias for a sparse vectors and write a function to compute
sparse product.

``` haskell literate
{-@ type SparseN a N = [(Btwn 0 N, a)] @-}
```

Since we know that all indexes are with the bounds of the source array
the following function verifies:

``` haskell literate
{-@ sparseProduct :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct :: Num a => Vector a -> [(Int, a)] -> a
sparseProduct x y = go 0 y
  where
    go acc [] = acc
    go acc ((i, v):ys) = go (acc + (x ! i) * v) ys
```

Another way to represend the *sparse product* is using `fold`. For
example:

``` haskell
foldl' :: (a -> b -> a) -> a -> [b] -> a
```

GHC infers that:

``` haskell
foldl' :: (a -> (Int, a)) -> a -> [(Int, a)] -> a
```

LH infers that:

``` haskell
b :: (Btwn 0 (vlen x), a)
```

``` haskell literate
{-@ sparseProduct' :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct' :: Num a => Vector a -> [(Int, a)] -> a
sparseProduct' x y = foldl' body 0 y
  where
    body sum (i, v) = sum + (x ! i) * v
```

Refined Datatypes.

``` haskell literate
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--no-total" @-}
```

``` haskell literate
module B3 where
```

``` haskell literate
import Prelude hiding (abs, length, min)
import Data.Vector hiding (singleton, foldl', foldr, fromList, (++), all)
import Data.Maybe (fromJust)
```

Sparse vectors revisited.

``` haskell literate
data Sparse a = SP
  { spDim :: Int
  , spElems :: [(Int, a)]
  }
```

  - `spDim` should be positive number
  - every index in `spElems` should be `0 <= i < spDim`

<!-- end list -->

``` haskell literate
{-@
data Sparse a = SP
  { spDim :: Nat
  , spElems :: [(Btwn 0 spDim, a)]
  }
@-}
```

``` haskell literate
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}
```

Now `SP` works like a *smart* constructor\!

``` haskell literate
okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog")
            ]
```

``` haskell
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog")
             ]
```

Field measures.

Lets write an alias for sparse vectors of size `N`.

``` haskell literate
{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}
```

Now we can write our `dotProd` function like this:

``` haskell literate
{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
  where
    go acc []          = acc
    go acc ((i, v):ys) = go (acc + (x ! i) * v) ys
```

And `fold`-based implementation:

Ex 5.1 (Sanitization)

``` haskell literate
{-@ fromList :: n:Nat -> [(Btwn 0 n, _)] -> Maybe (SparseN _ n) @-}
fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elems
  | all (< dim) (fst <$> elems) = Just $ SP dim elems
  | otherwise = Nothing
```

``` haskell literate
{-@ test1 :: SparseN String 3 @-}
test1 :: Sparse String
test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]
```

Ex 5.2 (Addition)

``` haskell literate
{-@ plus :: SparseN a 3 -> SparseN a 3 -> SparseN a 3 @-}
plus :: Sparse a -> Sparse a -> Sparse a
plus v1 v2 = SP (spDim v1) (spElems v1 ++ spElems v2)
```

But I think the goal is to make a general function that can work for any
dimension.

``` haskell literate
{-@ test2 :: SparseN Int 3 @-}
test2 :: Sparse Int
test2 = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]
```

Ordered lists.

``` haskell literate
data IncList a
  = Emp
  | (:<) { hd :: a, tl :: IncList a }
```

``` haskell literate
infixr 9 :<
```

We can specify that the elements are in order by refining *every*
element in `tl` to be *greater than* `hd`:

``` haskell literate
{-@
data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList {v:a | hd <= v} }
@-}
```

``` haskell literate
okList :: IncList Int
okList = 1 :< 2 :< 3 :< Emp
```

``` haskell
badList :: IncList Int
badList = 2 :< 1 :< 3 :< Emp
```

Insertion sort.

``` haskell literate
insertSort :: Ord a => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = insert x (insertSort xs)
```

``` haskell literate
insert :: Ord a => a -> IncList a -> IncList a
insert y Emp = y :< Emp
insert y (x :< xs)
  | y <= x = y :< x :< xs
  | otherwise = x :< insert y xs
```

Ex 5.3

``` haskell literate
insertSort' :: Ord a => [a] -> IncList a
insertSort' = foldr insert Emp
```

Merge sort.

``` haskell literate
split :: [a] -> ([a], [a])
split (x:y:zs) =
  let (xs, ys) = split zs
  in (x:xs, y:ys)
split xs = (xs, [])
```

Sometimes I get errors like http://ix.io/1N99 which really confuse me.

This is a “totality” error — it means your function/case expression is
missing a case and so LH cannot prove that case is dead code and hence
gives that error (e.g. the head or tail function which is not defined on
\[\]). This feature was added after the tutorial and the LH authors made
totality on by default. It can be switched off with `{-@ LIQUID
“—no-total” @-}`. Or of course it is better to implement the missing
case.

We should however add to the error the missing patterns…

One way to get them right now is load the file in ghci with the
`-fwarn-incomplete-patterns` flag.

``` haskell literate
merge :: Ord a => IncList a -> IncList a -> IncList a
merge Emp ys = ys
merge xs Emp = xs
merge (x :< xs) (y :< ys)
  | x <= y    = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys
```

``` haskell literate
mergeSort :: Ord a => [a] -> IncList a
mergeSort []  = Emp
mergeSort [x] = x :< Emp
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs) = split xs
```

Ex 5.4 (QuickSort)

``` haskell literate
quickSort :: Ord a => [a] -> IncList a
quickSort [] = Emp
quickSort (x:xs) = append x lessers greaters
  where
    lessers  = quickSort [y | y <- xs, y < x]
    greaters = quickSort [z | z <- xs, z >= x]
```

We need to ensure that `append` has a valid specification:

``` haskell literate
{-@
append
  :: x:a
  -> IncList {v:a | v < x}
  -> IncList {v:a | v >= x}
  -> IncList a
@-}
append :: Ord a => a -> IncList a -> IncList a -> IncList a
append z Emp ys       = z :< ys
append z (x :< xs) ys = x :< (append z xs ys)
```

Ordered trees.

``` haskell literate
data BST a
  = Leaf
  | Node { root  :: a
         , left  :: BST a
         , right :: BST a
         }
```

``` haskell literate
okBST :: BST Int
okBST =
  Node 6
    ( Node 2
      (Node 1 Leaf Leaf)
      (Node 4 Leaf Leaf)
    )
    ( Node 9
      (Node 7 Leaf Leaf)
      Leaf
    )
```

``` haskell literate
okBST' :: BST Int
okBST' =
  Node 5
    ( Node 3
      (Node 1 Leaf Leaf)
      (Node 4 Leaf Leaf)
    )
    ( Node 8
      (Node 7 Leaf Leaf)
      Leaf
    )
```

``` haskell literate
{-@
data BST a =
    Leaf
  | Node { root  :: a
         , left  :: BSTL a root
         , right :: BSTR a root
         }
@-}
```

``` haskell literate
{-@ type BSTL a X = BST {v:a | v < X} @-}
{-@ type BSTR a X = BST {v:a | v > X} @-}
```

``` haskell
badBST :: BST Int
badBST =
  Node 66
    ( Node 4
      (Node 1 Leaf Leaf)
      (Node 69 Leaf Leaf)
    )
    ( Node 99
      (Node 77 Leaf Leaf)
      Leaf
    )
```

Ex 5.5 (Duplicates)

The answer is no. Each value is either `>` than other or `<`. But `N >
N` is impossible and `N < N` doesn’t make any sense too.

Membership.

``` haskell literate
mem :: Ord a => a -> BST a -> Bool
mem _ Leaf = False
mem k (Node k' l r)
  | k == k'   = True
  | k <  k'   = mem k l
  | otherwise = mem k r
```

Singleton.

``` haskell literate
one :: a -> BST a
one x = Node x Leaf Leaf
```

Insertion.

``` haskell literate
add :: Ord a => a -> BST a -> BST a
add k' Leaf = one k'
add k' t@(Node k l r)
  | k' < k    = Node k (add k' l) r
  | k  < k'   = Node k l (add k' r)
  | otherwise = t
```

Minimum.

``` haskell literate
data MinPair a = MP
  { mEl :: a
  , mRest :: BST a
  }
```

``` haskell literate
{-@
data MinPair a = MP
  { mEl :: a
  , mRest :: BSTR a mEl
  }
@-}
```

Looks like the `delMin` example from page 55 needs an additional
restriction (that `BST a` isn’t just a `Leaf`) + maybe something else.

As I can see right now, nothing prevents `BST a` from being a `Leaf` So
`delMin Leaf = die "impossible"` branch is possible and verification
fails for me with error http://ix.io/1O9r.

``` haskell
{-@ delMin :: BST a -> MinPair a @-}
delMin :: Ord a => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r) =
  let MP k' l' = delMin l
  in MP k' (Node k l' r)
delMin Leaf = die "impossible"
```

Ex 5.6 (Delete)

Depends on `delMin`.

Ex 5.7. (Safely deleting minimum)

Depends on `delMin`.

Ex 5.8 (BST sort).

TODO\!

Lifting functions to Measures.

``` haskell literate
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
```

``` haskell literate
module B4 where
import Prelude hiding (head, tail, null, sum, foldl1)
import qualified Prelude as P
import A1 (safeDiv, die)
```

``` haskell literate
notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True
```

Measure is a *total* Haskell function:

  - single equation per data constructor
  - guaranteed to *terminate*

**measure** tells LiquidHaskell to *lift* a function into the refinement
logic:

``` haskell literate
{-@ measure notEmpty @-}
```

Now we can use the `notEmpty` predicate to describe non-empty lists:

``` haskell literate
{-@ type NEList a = { v:[a] | notEmpty v } @-}
```

`size` returns a non-zero value *if* the input list is not-empty. We
capture this condition with an implication in the output refinement.

``` haskell literate
{-@ size :: xs:[a] -> { v:Nat | notEmpty xs => v > 0 } @-}
size :: [a] -> Int
size []     = 0
size (_:xs) = 1 + size xs
```

``` haskell literate
{-@ average :: NEList Int -> Int @-}
average :: [Int] -> Int
average xs = total `safeDiv` elems
  where
    total = P.sum xs
    elems = size xs
```

Ex 6.1 (Average, Maybe)

``` haskell literate
average' :: [Int] -> Maybe Int
average' xs
  | elems > 0 = Just $ (P.sum xs) `safeDiv` elems
  | otherwise = Nothing
  where
    elems = size xs
```

Ex 6.2 (Debugging specificatins)

These two examples below are rejected because the `xs` in `(_:xs)` could
be empty:

``` haskell
{-@ size1 :: xs:NEList a -> Pos @-}
size1 :: [a] -> Int
size1 [] = 0
size1 (_:xs) = 1 + size1 xs
```

``` haskell
{-@ size2 :: xs:[a] -> { v:Int | notEmpty xs => v > 0 } @-}
size2 :: [a] -> Int
size2 [] = 0
size2 (_:xs) = 1 + size2 xs
```

Since we have `NEList` we can use it to type the `head` and `tail`
functions:

``` haskell literate
{-@ head :: NEList a -> a @-}
head :: [a] -> a
head (x:_) = x
head []    = die "fear not"
```

``` haskell literate
{-@ tail :: NEList a -> [a] @-}
tail :: [a] -> [a]
tail (_:xs) = xs
tail []    = die "fear not"
```

LH uses the precondition to deduce that the second equations are *dead
code*.

Ex 6.3 (Safe head)

``` haskell literate
safeHead :: [a] -> Maybe a
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs
```

``` haskell literate
{-@ null :: xs:[a] -> {v:Bool | v <=> not notEmpty xs } @-}
null :: [a] -> Bool
null []    = True
null (_:_) = False
```

Groups.

Lets write a function that chunks sequences into non-empty groups of
equal elements:

``` haskell literate
{-@ groupEq :: Eq a => [a] -> [NEList a] @-}
groupEq :: Ord a => [a] -> [[a]]
groupEq []     = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys, zs) = span (x ==) xs
```

Eliminate stuttering:

``` haskell literate
eliminateStutter :: String -> String
eliminateStutter = map head . groupEq
```

``` haskell
λ> eliminateStutter "ssstringssss liiiiiike thisss"
"strings like this"
```

``` haskell literate
{-@ foldl1 :: (a -> a -> a) -> NEList a -> a @-}
foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs) = foldl f x xs
foldl1 _ [] = die "foldl1"
```

Sum of a non-empty list of `Num a`:

``` haskell literate
{-@ sum :: Num a => NEList a -> a @-}
sum :: Num a => [a] -> a
sum [] = die "sum"
sum xs = foldl1 (+) xs
```

``` haskell literate
sumOk :: Int
sumOk = sum [1, 2, 3]
```

``` haskell
sumBad :: Int
sumBad = sum []
```

``` haskell
sumBad' :: Int
sumBad' = sum [1..3]
```

Ex 6.4 (Weighted average)

``` haskell literate
{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage :: [(Int, Int)] -> Int
wtAverage wxs = totElems `safeDiv` totWeight
  where
    elems     = map' (uncurry (*)) wxs
    weights   = map' fst wxs
    totElems  = sum' elems
    totWeight = sum' weights
```

``` haskell literate
{-@ sum' :: NEList Pos -> Pos @-}
sum' :: [Int] -> Int
sum' [] = die "sum"
sum' xs = foldl1 (+) xs
```

``` haskell literate
{-@ map' :: (a -> b) -> NEList a -> NEList b @-}
map' :: (a -> b) -> [a] -> [b]
map' _ []     = die "impossible"
map' f (x:[]) = [f x]
map' f (x:xs) = (f x) : map' f xs
```

Ex 6.5 (Mitchell’s risers)

``` haskell literate
{-@ risers :: Ord a => NEList a -> NEList [a] @-}
risers :: (Ord a) => [a] -> [[a]]
risers []  = die "impossible"
risers [x] = [[x]]
risers (x:y:etc)
  | x <= y    = (x:s):ss
  | otherwise = [x]:(s:ss)
  where
    (s, ss) = safeSplit $ risers (y:etc)
```

``` haskell literate
{-@ safeSplit :: NEList a -> (a, [a]) @-}
safeSplit :: [a] -> (a, [a])
safeSplit (x:xs) = (x, xs)
safeSplit _ = die "go forth and die"
```

Numeric measures.

Wholemeal programming.

``` haskell literate
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
```

``` haskell literate
module B5 where
import Prelude
```

We can use **measures** to specify dimensions and create a
dimension-aware API for lists which can be used to implement wholemeal
dimension-safe APIs.

``` haskell literate
data Vector a = V
  { vDim :: Int
  , vEls :: [a]
  }
  deriving (Eq)
```

``` haskell literate
data Matrix a = M
  { mRow :: Int
  , mCol :: Int
  , mEls :: Vector (Vector a)
  }
  deriving (Eq)
```

``` haskell literate
dotProd :: Num a => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    prod = zipWith (*)
    xs   = vEls vx
    ys   = vEls vy
```

``` haskell literate
matProd :: Num a => Matrix a -> Matrix a -> Matrix a
matProd (M rx _ xs) (M _ cy ys) = M rx cy els
  where
    els = for xs $ \xi ->
            for ys $ \yj ->
              dotProd xi yj
```

``` haskell literate
for :: Vector a -> (a -> b) -> Vector b
for (V n xs) f = V n (f <$> xs)
```

We need a way to represent the *dimensions*. **Measures** are ideal for
this task, so lets write a measure to describe the length of a list:

``` haskell literate
{-@ measure size @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs
```

Just a reminder: a **measure** is an *inductively defined function* with
a single equative per data-constructor.

As with *refined data definitions*, the measures are translated into
smth like this:

``` haskell
data [a] where
  []  :: { v:[a] | size v = 0 }
  (:) :: a -> xs:[a] -> { v:[a] | size v = 1 + size xs }
```

Multiple measures may be defined for the same data type, for example:

``` haskell literate
{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True
```

Different measures can be composed by *conjoining* the refinements. For
example, lets compose `size` and `notEmpty` measures:

``` haskell
data [a] where
  []  :: { v:[a] | not (notEmpty v) size v = 0 }
  (:) :: a
      -> xs:[a]
      -> { v:[a] | notEmpty v && size v = 1 + size xs }
```

**Measure**’s decouples *property* from *structure*, which enabled the
use of the same structure for many different purposes.
