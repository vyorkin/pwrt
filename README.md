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

``` {.haskell .literate}
module A1 where
```

Base types, type variables:

``` {.haskell}
b := Int | Bool | ... | a, b, c
```

Refined base or refined function:

``` {.haskell}
t := { x:b | p } | x:t -> t
```

Where `p` is a predicate in decidable logic:

``` {.haskell}
p := e          -- atom
  | e1 == e2    -- equality
  | e1 <  e2    -- ordering
  | (p && p)    -- and
  | (p || p)    -- or
  | (not p)     -- negation
```

Where `e` is an expression:

``` {.haskell}
e := x, y, z,...    -- variable
   | 0, 1, 2,...    -- constant
   | (e + e)        -- addition
   | (e - e)        -- subtraction
   | (c * e)        -- linear multiplication
   | (f e1 ... en)  -- uninterpreted function
```

Ok, lets try something!

We use `{-@ ... @-}` to add refinement type annotations:

``` {.haskell .literate}
{-@ type Zero = {v:Int | v = 0} @-}
{-@ zero :: Zero @-}
zero :: Int
zero = 0
```

Natural numbers:

``` {.haskell .literate}
{-@ type Nat = {v:Int | 0 <= v} @-}
{-@ nats :: [Nat] @-}
nats :: [Int]
nats = [0, 1, 2]
```

Positive integers:

``` {.haskell .literate}
{-@ type Pos = {v:Int | 1 <= v} @-}
```

``` {.haskell .literate}
{-@ pos :: [Pos] @-}
pos :: [Int]
pos = [1, 2, 3]
```

Predicate Subtyping:

``` {.haskell .literate}
{-@ z :: Zero @-}
z :: Int
z = 0
```

Because `z :: Zero <: Nat`:

``` {.haskell .literate}
{-@ z' :: Nat @-}
z' :: Int
z' = z
```

Contracts (function types):

If the program type checks it means that `impossible` is never called at
runtime.

``` {.haskell .literate}
{-@ impossible :: {v:_ | false} -> a @-}
impossible :: [Char] -> a
impossible msg = error msg
```

Pre-conditions:

The next example won't typecheck:

``` {.haskell}
{-@ safeDiv :: Int -> Int -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n
```

But this one will:

``` {.haskell .literate}
{-@ type NonZero = {v:Int | v /= 0} @-}
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
safeDiv :: Int -> Int -> Int
safeDiv x n = x `div` n
```

Verifying user input:

``` {.haskell .literate}
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

``` {.haskell .literate}
{-@ foo :: Int -> Maybe {v:Int | v /= 0} @-}
foo :: Int -> Maybe Int
foo 0 = Nothing
foo n = Just n
```

``` {.haskell}
...
case foo d of
Nothing -> putStrLn "Blya"
Just n  -> ...
...
```

Won't typecheck (`n` could be `0`)

``` {.haskell .literate}
avg :: [Int] -> Int
avg xs = safeDiv total n
  where
    total = sum xs
    n = size xs
```

We could specify **post-condition** as **output-type**:

``` {.haskell .literate}
{-@ size :: [a] -> Pos @-}
size :: [a] -> Int
size []     = 1
size (_:xs) = 1 + size xs
```
