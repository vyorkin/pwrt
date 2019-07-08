Refinement Types = `Types` + `Predicates`.

> module A1
>   ( minus
>   ) where

Base types, type variables:

< b := Int | Bool | ... | a, b, c

Refined base or refined function:

< t := { x:b | p } | x:t -> t

The very basic example:

> {-@ minus :: x:Int -> y:Int -> {v:Int | v = x - y} @-}
> minus :: Int -> Int -> Int
> minus x y = x - y

Blah

> {-@ plus :: x:Int -> y:Int -> {v:Int | v = x + y} @-}
> plus :: Int -> Int -> Int
> plus x y = x + y

> test :: String -> (String, String)
> test x = ("test", x)

Quux

> {-@ quux :: x:Int -> y:Int -> z:Int -> {v:Int | v = x + y - z} @-}
> quux :: Int -> Int -> Int -> Int
> quux x y z = x `plus` y `minus` z

Blah blah
