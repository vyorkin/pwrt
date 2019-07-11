

Refinement Types = `Types` + `Predicates`.

**Refinement types** allows us to decorate types with _logical predicates_,
that contrain the set of values described by the type.

> module A1 where

> {-@ LIQUID "--no-termination" @-}

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

> {-@ type Zero = {v:Int | v = 0} @-}
> {-@ zero :: Zero @-}
> zero :: Int
> zero = 0

Predicate Subtyping:

> {-@ type Nat   = {v:Int | 0 <= v}        @-}
> {-@ type Even  = {v:Int | v mod 2 == 0 } @-}
> {-@ type Lt100 = {v:Int | v < 100}       @-}

Natural numbers:

> {-@ nats :: [Nat] @-}
> nats :: [Int]
> nats = [0, 1, 2]

Positive integers:

> {-@ type Pos = {v:Int | 1 <= v} @-}

> {-@ pos :: [Pos] @-}
> pos :: [Int]
> pos = [1, 2, 3]

Zero:

> {-@ z :: Zero @-}
> z :: Int
> z = 0

Because `z :: Zero <: Nat`:

> {-@ z' :: Nat @-}
> z' :: Int
> z' = z

Also:

> {-@ z'' :: Even @-}
> z'' :: Int
> z'' = z

And this one as well:

> {-@ z''' :: Lt100 @-}
> z''' :: Int
> z''' = z

When we _erase_ the _refinement_ we get the standart Haskell types.
For example, the `Int` is equivalent to `{v:Int | true}` because
any standart Haskell type has the trivial refinement  `true`.

Writing specifications and _typing dead code_.

Contracts (function types):

If the program type checks it means
that `impossible` is never called at runtime.

> {-@ impossible :: {v:String | false} -> a @-}
> impossible :: String -> a
> impossible msg = error msg

> {-@ die :: {v:String | false} -> a @-}
> die :: String -> a
> die msg = impossible msg

For example, LH will _accept_:

> cannonDie :: ()
> cannonDie =
>   if 1 + 1 == 3
>   then die "horrible death"
>   else ()

But will _reject_:

< canDie :: ()
< canDie =
<   if 1 + 1 == 2
<   then die "horrible death"
<   else ()

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
>   calc

Post-conditons.

We can specify a _post-condition_ as _output-type_.

For example, lets refine the output type of the `abs` function
to say that it returns only non-negative values:

> {-@ abs :: Int -> Nat @-}
> abs :: Int -> Int
> abs n
>   | 0 < n = n
>   | otherwise = -n

Because SMT solver has built-in decision procedures for arithmetic.

Ex 3.1:

> avg :: [Int] -> Int
> avg xs = safeDiv total n
>   where
>     total = sum xs
>     n = size xs

> {-@ size :: [a] -> Pos @-}
> size :: [a] -> Int
> size []     = 1
> size (_:xs) = 1 + size xs

Another way to solve the `calc` exercise is
to define a function like:

> {-@ nonZero :: Int -> Maybe {v:Int | v /= 0} @-}
> nonZero :: Int -> Maybe Int
> nonZero 0 = Nothing
> nonZero n = Just n

< ...
< case nonZero d of
<   Nothing -> putStrLn "Blya"
<   Just n  -> ...
< ...

Or

> result :: Int -> Int -> String
> result n d
>   | isPositive d = "result = " ++ show (n `safeDiv` d)
>   | otherwise    = "blya"

Ex 3.2:

> {-@ isPositive :: x:_ -> {v:Bool | v <=> x > 0} @-}
> isPositive :: (Ord a, Num a) => a -> Bool
> isPositive = (> 0)

> calc' :: IO ()
> calc' = do
>   putStrLn "n: "
>   n <- readLn
>   putStrLn "d: "
>   d <- readLn
>   putStrLn $ result n d
>   calc

Ex 3.3: Assertions

> {-@ lAssert :: {v:Bool | v} -> a -> a @-}
> lAssert :: Bool -> a -> a
> lAssert True x  = x
> lAssert False _ = die "assertion failed!"

> yes = lAssert (1 + 1 == 2) ()

< no  = lAssert (1 + 1 == 3) ()
