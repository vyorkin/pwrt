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
module A1
  ( minus
  ) where
```

Base types, type variables:

``` {.haskell}
b := Int | Bool | ... | a, b, c
```

Refined base or refined function:

``` {.haskell}
t := { x:b | p } | x:t -> t
```

The very basic example:

``` {.haskell .literate}
{-@ minus :: x:Int -> y:Int -> {v:Int | v = x - y} @-}
minus :: Int -> Int -> Int
minus x y = x - y
```

Blah

``` {.haskell .literate}
{-@ plus :: x:Int -> y:Int -> {v:Int | v = x + y} @-}
plus :: Int -> Int -> Int
plus x y = x + y
```

``` {.haskell .literate}
test :: String -> (String, String)
test x = ("test", x)
```

Quux

``` {.haskell .literate}
{-@ quux :: x:Int -> y:Int -> z:Int -> {v:Int | v = x + y - z} @-}
quux :: Int -> Int -> Int -> Int
quux x y z = x `plus` y `minus` z
```

Blah blah
