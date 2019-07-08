> module A2 where

> import A1
> import Prelude hiding (length, foldr1, foldr, map, init)

> data List a
>   = Emp
>   | a ::: List a

Measures:

> {-@ measure length @-}
> length :: List a -> Int
> length Emp = 0
> length (_ ::: xs) = 1 + length xs

And now LH knows the following properties about our `List a`:

< data List a where
<   Emp   :: {v:List a | length v = 0}
<   (:::) :: x:a -> xs:List a
<         -> {v:List a | length v = 1 + length xs}

Lets make a type alias for a non-empty `List`:

> {-@ type ListNE a = {v:List a | length v > 0} @-}

And now `head` and `tail` functions are not _partial_ anymore:

> {-@ head :: ListNE a -> a @-}
> head (x ::: _) = x

> {-@ tail :: ListNE a -> List a @-}
> tail (_ ::: xs) = xs

_Fold_ `f` over list initially using _first_ element:

> {-@ foldr1 :: (a -> a -> a) -> ListNE a -> a @-}
> foldr1 :: (a -> a -> a) -> List a -> a
> foldr1 f (x ::: xs) = foldr f x xs
> foldr1 _ _          = impossible "foldr1"

> foldr :: (a -> b -> b) -> b -> List a -> b
> foldr _ acc Emp = acc
> foldr f acc (x ::: xs) = f x (foldr f acc xs)

Another average:

> {-@ average' :: ListNE Int -> Int @-}
> average' :: List Int -> Int
> average' xs = total `div` n
>   where
>     total = foldr1 (+) xs
>     n = length xs

We can refine data types and make illegal states unrepresentable.
For example, lets make sure that every year has exactly 12 months.

> data Year a = Year (List a)

> {-@ data Year a = Year (ListN a 12) @-}

We need a type for lists of a given size.

> {-@ type ListN a N = {v: List a | length v == N } @-}

Now, this won't typecheck:

< badYear :: Year Int
< badYear = Year (1 ::: Emp)

Mapping:

> {-@ map :: (a -> b) -> xs:List a -> ys:ListN b {length xs} @-}
> map :: (a -> b) -> List a -> List b
> map _ Emp = Emp
> map f (x ::: xs) = f x ::: map f xs

Lets write a function to calculate an average temperature of the year:

> data Weather = W { temp :: Int, rain :: Int }

> tempAverage :: Year Weather -> Int
> tempAverage (Year ms) = average' months
>   where
>     months = map temp ms

Another example:

> {-@ init :: (Int -> a) -> n:Nat -> ListN a n @-}
> init :: (Int -> a) -> Int -> List a
> init _ 0 = Emp
> init f n = f n ::: init f (n - 1)

> sanDiegoTemp :: Year Int
> sanDiegoTemp = Year (init (const 72) 12)
