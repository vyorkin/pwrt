
Refinement Types = `Types` + `Predicates`.

> module A1 where

Base types, type variables:

< b := Int | Bool | ... | a, b, c

Refined base or refined function:

< t := { x:b | p } | x:t -> t

Where `p` is a predicate in decidable logic:

< p := e          -- atom
<   | e1 == e2    -- equality
<   | e1 <  e2    -- ordering
<   | (p && p)    -- and
<   | (p || p)    -- or
<   | (not p)     -- negation

Where `e` is an expression:

< e := x, y, z,...    -- variable
<    | 0, 1, 2,...    -- constant
<    | (e + e)        -- addition
<    | (e - e)        -- subtraction
<    | (c * e)        -- linear multiplication
<    | (f e1 ... en)  -- uninterpreted function

Ok, lets try something!

We use `{-@ ... @-}` to add refinement type annotations:

< {-@ type Zero = {v:Int | v = 0} @-}
< {-@ zero :: Zero @-}
< zero :: Int
< zero = 0

Natural numbers:

> {-@ type Nat = {v:Int | 0 <= v} @-}
> {-@ nats :: [Nat] @-}
> nats :: [Int]
> nats = [0, 1, 2]

Positive integers:

> {-@ type Pos = {v:Int | 1 <= v} @-}

> {-@ pos :: [Pos] @-}
> pos :: [Int]
> pos = [1, 2, 3]

Predicate Subtyping:

< {-@ z :: Zero @-}
< z :: Int
< z = 0

Because `z :: Zero <: Nat`:

< {-@ z' :: Nat @-}
< z' :: Int
< z' = z

Contracts (function types):

If the program type checks it means
that `impossible` is never called at runtime.

> {-@ impossible :: {v:_ | false} -> a @-}
> impossible :: [Char] -> a
> impossible msg = error msg

Pre-conditions:

The next example won't typecheck:

< {-@ safeDiv :: Int -> Int -> Int @-}
< safeDiv :: Int -> Int -> Int
< safeDiv _ 0 = impossible "divide-by-zero"
< safeDiv x n = x `div` n

But this one will:

> {-@ type NonZero = {v:Int | v /= 0} @-}
> {-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
> safeDiv :: Int -> Int -> Int
> safeDiv x n = x `div` n

Verifying user input:

> calc :: IO ()
> calc = do
>   putStrLn "Enter numerator"
>   n <- readLn
>   putStrLn "Enter denominator"
>   d <- readLn
>   if d == 0
>     then putStrLn "Blya"
>     else putStrLn ("Result = " ++ show (safeDiv n d))
>   -- calc

Another way could be:

> {-@ foo :: Int -> Maybe {v:Int | v /= 0} @-}
> foo :: Int -> Maybe Int
> foo 0 = Nothing
> foo n = Just n

< ...
< case foo d of
< Nothing -> putStrLn "Blya"
< Just n  -> ...
< ...

Won't typecheck (`n` could be `0`)

> avg :: [Int] -> Int
> avg xs = safeDiv total n
>   where
>     total = sum xs
>     n = size xs

We could specify **post-condition** as **output-type**:

> {-@ size :: [a] -> Pos @-}
> size :: [a] -> Int
> size []     = 1
> size (_:xs) = 1 + size xs
