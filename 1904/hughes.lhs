> module Hughes where
> import Prelude hiding (sum, product, (++), length, map, filter, repeat, sqrt)

An attempt to give Haskell implementations of the example
(Miranda like) programs of Hughes' 1989 classic "Why does
functional programming matter".

Sections 1 and 2 are introductory, programming examples start
in Section 3.

3. Gluing functions together

Hughes starts with lists. This is of course all standard,
so we just cite the library definitions. Here is the
list type as defined in GHC.Types (try ":info []" in ghci!): 

< data [] a = [] | a : [a] 

Note that [] on the left is a type constructor, [] on the
right is the data constructor for the empty list.

Hughes' "reduce" which he writes like this

(reduce (⊕) (⊗) [] = x
(reduce (⊕) (⊗) (el:list) = el ⊕ (reduce (⊕) x list)

is called "foldr" in Haskell:

< foldr :: (a -> b -> b) -> b -> [a] -> b
< foldr op base [] = base
< foldr op base (x:xs) = x `op` (foldr op base xs)

Note that in current GHC (the most popular modern Haskell
system), foldr is no longer literally defined like this:
foldr now has a more general type (it works on all types in
a the type class "Foldable" - try ":t foldr" in ghci!).
But of course [] is in Foldable, and GHC's foldr
implementation is equivalent to the above.

We can now implement Hughes` reduce examples with foldr.

We will always write explicit type declarations. Haskell
(like Miranda) doesn't need them, it has powerful type
inference built in. They are here to help us humans
understand what we're doing. Often the types inferred by
the type checker will be more general than the ones we
give (try e.g. ":t foldr (+) 0" in ghci!). But although
Hughes recommends to look for generalizations, let's keep
it simple for now.

> sum :: [Int] -> Int
> sum = foldr (+) 0

> product :: [Int] -> Int
> product = foldr (*) 1

Using

< data Bool = False | True

with the binary operations

< (&&),(||) :: Bool -> Bool -> Bool

we can write

> alltrue, anytrue :: [Bool] -> Bool
> alltrue = foldr (&&) True
> anytrue = foldr (||) False

Concatenation of two lists can be written with a fold:

> (++) :: [a] -> [a] -> [a]
> (++) xs ys = foldr (:) ys xs

The length of a list:

> length :: [a] -> Int
> length = foldr (\el -> \len -> (1 + len)) 0

Here (\x -> t) is notation for a the Lambda
abstraction λ x. t (where x is the variable bound
by the lambda - it may, but does not have to, occur
as a free variable in term t).

Finally we have map (making List a functor!):

> map :: (a -> b) -> ([a] -> [b])
> map f = foldr (\x -> \xs -> (f x : xs)) []

which can be used e.g. to sum over lists of lists,
a.k.a. matrices

> summatrix :: [[Int]] -> Int
> summatrix = sum . map sum

where "." is concatenation of functions, i.e.

< (.) :: (b -> c) -> (a -> b) -> a -> c
< (f . g) x = f (g x)

Next Hughes considers trees. He gives the type

treeof α ::= α @ (listof (treeof α))

which we write

> data Tree l = Node l [Tree l] deriving Show

The single constructor [Node] of [Tree] has type:

< Node :: l -> [Tree l] -> Tree l

> exampleTree :: Tree(Int)
> exampleTree = Node 1 [Node 2 [], Node 3 [Node 4 []]]

Hughes gives redtree as an analog to his reduce or our foldr
in an ad hoc manner using a mutual recursion

< redtree  (⊕) (⊗) a (label @ subtrees) = label ⊕ redtree' (⊕) (⊗) a subtrees)
< redtree' (⊕) (⊗) a [] = a
< redtree' (⊕) (⊗) a (subtree:rest) = (redtree (⊕) (⊗) a subtree) ⊗ (redtree' (⊕) (⊗) a rest) 

We can deduce types for these functions:

> redtree  :: (l -> a -> r) -> (r -> a -> a) -> a -> (Tree l) -> r
> redtree' :: (l -> a -> r) -> (r -> a -> a) -> a -> [Tree l] -> a   

Here l is the label type, r the result type of redtree and a the result 
type of redtree' (which by the first redtree'-pattern above is just the 
type of the argument a). The types of ⊕ and ⊗ then have to be as given.

> redtree  plus times a (Node label subtrees) = label `plus` redtree' plus times a subtrees
> redtree' plus times a [] = a
> redtree' plus times a (subtree:rest) = redtree plus times a subtree `times` redtree' plus times a rest

* Interlude: Folds for inductive datatypes

A fold for a datatype D produces functions D -> b out of
D. By category theory, there is a unique function of this
type for any F-algebra-structure on b, where F is the 
"structure-" or "signature-functor" for D, which is
determined by the types of the construcors of D.

Down to earth this means: for each constructor C of D that 
has type T we have to provide a term c (generally a function 
into b) of type T[b/D] obtained by replacing any occurence 
of D in T by b.

For Tree, we have just one constructor and by the above,
foldTree has to have the following type:

> foldTree :: (l -> [r] -> r) -> Tree l -> r

The implementation by pattern matching follows this recipe:
for any constructor C of D, the fold reduces a generic term
of D built with constructor C to an application of 
the corresponding c. Constructor arguments of type D 
are replaced by recursive calls, other arguments are
just passed to c.

> foldTree g (Node l ts) = g l (map (foldTree g) ts)

Note that here the recursive argument is a list of trees, so
we have to do the recursive call on each tree in this list,
which is achieved using "map".

Well, if this is the "general" fold, we should be able to
express redtree by foldTree. More specifically, there should be

> gFromPTA :: (l -> a -> r) -> (r -> a -> a) -> a -> (l -> [r] -> r)

such that for any plus, times, a and tree of the appropriate types
we have

redtree plus times a tree = foldTree (gFromPTA plus time a) tree

Let's fix plus, times and a and abbreviate

rt  = redtree  plus times a   and
rt' = redtree' plus times a

Then

< rt  (Node ts l) = l `plus` rt' ts
< rt' [] = a
< rt' (t:ts) = rt t `times` rt' ts

We observe

  rt' = (foldr times a) . (map rt)

Proof. By structural induction on [Tree l].

 case []:

  (foldr `times` a) (map rt [])
 ={ def. map }
  (foldr `times` a) []
 ={ def. foldr }
  a
 ={ def. rt' }= 
  rt' []

 case (t:ts):

  (foldr `times` a) (map rt (t:ts))
 ={ def. map } 
  (foldr `times` a) (rt t : map rt ts)
 ={ def. foldr } 
  rt t `times` (foldr `times` a) (map rt ts)
 ={ ind. hyp. }
  rt t `times` rt' ts
 ={ def. rt' }=
  rt' (t:ts)

Thus, using foldr and map, we can get rid of the mutual recursion
and just write

< rt (Node ts l) = l `plus` ((foldr `times` a ) . (map rt))

So we can indeed implement gFromPTA as

> gFromPTA plus times a l rs = l `plus` (foldr times a) rs

and reimplement redtree using foldTree:

> foldTreeH :: (l -> a -> r) -> (r -> a -> a) -> a -> (Tree l) -> r
> foldTreeH plus times a = foldTree (gFromPTA plus times a)

We give Hughes' examples:

> sumtree :: Tree(Int) -> Int
> sumtree = foldTreeH (+) (+) 0
>
> labels :: Tree(l) -> [l]
> labels = foldTreeH (:) (++) []
>
> maptree :: (l -> l') -> Tree(l) -> Tree(l')
> maptree f = foldTreeH op (:) []  
>    where label `op` subtrees = Node (f label) subtrees


* More on trees 

** Special case: give g in foldTree as a foldr

< foldTree' :: (r -> (l -> r) -> (l -> r)) -> (l -> r) -> Tree l -> r
< foldTree' h n = foldTree (foldr h n)

We have: for each h, n and tree of the appropriate types

foldTree' h n tree = foldTreeH (flip ($)) c n

Problem: Can we simulate redtree (⊕) (⊗) a  with foldTree' c n ?
Probably not.

** unfold

> unfoldTree :: (s -> (l,[s])) -> s -> Tree(l)
> unfoldTree gen seed = Node l subtrees  where
>         genStep  = gen seed
>         l        = fst genStep
>         subtrees = map (unfoldTree gen) (snd genStep)

can be used to generate tree examples

> filter :: (l->Bool) -> [l] -> [l]
> filter p = foldr op []  where
>    op x xs = if p x then (x:xs) else xs

proper divisors of an integer

> divs :: Integer -> [Integer]
> divs n = filter (\d -> n `mod` d == 0) [2..(n-1)]

build a tree of proper divisors...

> divsTree :: Integer -> Tree(Integer)
> divsTree = unfoldTree (\n -> (n, divs n))

4. Gluing programs together
4.1 Newton-Raphson square roots

> next :: Double -> Double -> Double
> next n x = (x + n/x)/2
>
> repeat :: (a -> a) -> a -> [a]
> repeat f a = a : repeat f (f a)

> within :: Double -> [Double] -> Double
> within eps (a:b:rest) =
>   if abs(a-b) <= eps
>   then b
>   else within eps (b:rest)

> sqrt :: Double -> Double -> Double -> Double
> sqrt a0 eps n = within eps (repeat (next n) a0)

> relative :: Double -> [Double] -> Double
> relative eps (a:b:rest) =
>   if (a/b - 1) <= eps
>   then b
>   else relative eps (b:rest)

> relativesqrt :: Double -> Double -> Double -> Double
> relativesqrt a0 eps n = relative eps (repeat (next n) a0)

4.2 Numerical differentiation

> easydiff :: (Double -> Double) -> Double -> Double -> Double
> easydiff f x h = (f (x + h) - f x) / h

> differentiate :: Double -> (Double -> Double) -> Double -> [Double]
> differentiate h0 f x = map (easydiff f x) (repeat (\h -> h/2) h0)


t.b.c.









