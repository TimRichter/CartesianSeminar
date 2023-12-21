{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Float renaming (primFloatSqrt to sqrt)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Nat hiding (_+_;_*_;_^_;_<_;_≤_;∣_-_∣)
open import Data.List hiding (head; tail; take; zip)
open import Function.Base using (_∘_ ; id; flip)
open import Data.Product

-- Implementation of parts of Halfant, Sussmann - 1988 - "Abstraction in Numerical Methods"

module HalfantSussman where

-- Preliminaries: operations on floats

infixl 20 _+_
infixl 20 _-_
infixl 19 _*_
infixl 18 _/_
infixl 17 _^_

_+_ _-_ _*_ _/_ _^_ : Float → Float → Float
_+_ = primFloatPlus
_-_ = primFloatMinus
_*_ = primFloatTimes
_/_ = primFloatDiv

-- in Agda versions prior to 2.6.2, there was no primFloatPow
-- (and primFloatExp and primFloatLog were named differently).
-- So, for Agda versions ≥ 2.6.2
_^_ = primFloatPow
-- for older versions:
-- x ^ y = primExp ((primLog x) * y)


ln : Float → Float → Float
ln base x = primFloatLog x / primFloatLog base

infix 16 _<_
infix 16 _≤_

_<_ _≤_ : Float → Float → Bool
_<_ = primFloatLess
x ≤ y = not (y < x)

infix 15 ∣_∣

∣_∣  : Float → Float   -- ∣ is typed as \|
∣ x ∣ with (x < 0.0)
... | false = x
... | true  = primFloatNegate x

-- Streams  ... our first example of a coinductive type

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public

-- streams (or functions into streams) can be defined
-- by copattern matching (or, what amounts to the same, by unfold, see below)

constStream5 : Stream ℕ
head constStream5 = 5
tail constStream5 = constStream5


-- we can "take" an arbitrarily long initial segment of a stream
-- (which will be a list)
take : {A : Set} → ℕ → Stream A → List A
take zero    as = []
take (suc n) as = (head as) ∷ (take n (tail as))

-- we can "lookup" any entry in a stream
infix 25 _!!_
_!!_ : {A : Set} → Stream A → ℕ → A
as !! zero = head as
as !! (suc n) = tail as !! n

-- conversely, given a function ℕ → A , we can
-- form the stream  f 0 , f 1 , ...
fun2Stream : {A : Set} → (ℕ → A) → Stream A
head (fun2Stream f) = f zero
tail (fun2Stream f) = fun2Stream (f ∘ suc)

-- given an endofunction f of some type A and a "starting point" a : A
-- (this data is often referred to as a "dynamical system on A")
-- we can compute the stream   a , f a , f (f a) ,...
stream-of-iterations : {A : Set} → (A → A) → A → Stream A
Stream.head (stream-of-iterations next value) = value
Stream.tail (stream-of-iterations next value) = stream-of-iterations next (next value)


-- complete the following definition
flow : {A : Set} → (A → A) → ℕ → A → A
flow next zero    = id
flow next (suc n) = next ∘ (flow next n)

-- e.g. compute flow next 2:
-- flow next (suc (suc zero)) a = next (flow next (suc zero) a)
--                              = next (next (flow next zero a))
--                              = next (next (a))
-- i.e. flow next 2 is (extensionally) equal to   next ∘ next

-- Tim: when I gave the exercise, I had in mind:
-- ℕ → A    and    Stream A   are  "the same" (isomorphic,
-- in bijection, equivalent...) via the functions fun2Stream and _!!_
-- and flow is nothing else than  stream-of-iterations transported
-- along this equivalence ... What I missed was: stream-of-iterations f
-- isn't a stream but of type  A → Stream A ...
-- So we have to postcompose with _!!_ to get someting of
-- type  A → ℕ → A, and flip this binary function to get the flow:

flow' : {A : Set} → (A → A) → ℕ → A → A
flow' = flip ∘ (_!!_ ∘_) ∘ stream-of-iterations

-- flow f n  is usually written f^n
-- flow next 0 ≐ id
-- flow next (n + m) ≐ flow next n ∘ flow next m

-- examples for streams

-- 0, 1, 2, 3, ...
allℕ : Stream ℕ
allℕ = stream-of-iterations suc zero

-- a, a, a, ....
constStream : {A : Set} → A → Stream A
constStream a = stream-of-iterations id a


-- on with the article:

refine-by-doubling : Float → Float
refine-by-doubling s = s / sqrt (2.0 + sqrt (4.0 - s * s))

side-lengths : Stream Float
side-lengths = stream-of-iterations refine-by-doubling (sqrt 2.0)

side-numbers : Stream Float
side-numbers = stream-of-iterations (λ x → 2.0 * x) 4.0

semi-perimeter : Float → Float → Float
semi-perimeter length-of-side number-of-sides = (number-of-sides / 2.0) * length-of-side

map-streams : {A B : Set} → (A → B) → Stream A → Stream B
head (map-streams f as) = f (head as)
tail (map-streams f as) = map-streams f (tail as)

zip-streams : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zip-streams op as bs) = op (head as) (head bs)
tail (zip-streams op as bs) = zip-streams op (tail as) (tail bs)

archimedean-pi-sequence : Stream Float
archimedean-pi-sequence = zip-streams semi-perimeter side-lengths side-numbers

-- Extrapolation gives a "better" sequence of approximations for pi:
--
-- Qₙ := 1/3 * (4P₂ₙ - Pₙ)

q : Float → Float → Float
q p tp = (4.0 * tp - p) / 3.0

better-pi-sequence : Stream Float
better-pi-sequence =
  let
    aseq = archimedean-pi-sequence
  in
    zip-streams q aseq (tail aseq)

-- Exercise: Apply the same idea again eliminate the term with 1/n^4
-- and thus get a stream converging even faster to pi

even-better-pi-sequence : Stream Float
even-better-pi-sequence =
  let
    bseq = better-pi-sequence
    q' : Float → Float → Float
    q' q tq = (16.0 * tq - q) / 15.0
  in
    zip-streams q' bseq (tail bseq)

-- Already the 6th term of even-better-pi-sequence has
-- 15 digits of π correct.  However, after that it doesn't
-- get better and instead oscillates... to be discussed.

-- Determine approximation order
---------------------------------
{-
At the end of page 2, the paper says "Alternatively, the
appropriate exponent p for a given column can be inferred
numerically from the early terms of that column;..."

Suppose we are given a stream s₀, s₁, s₂, ...
(of Floats...). We assume (Ansatz!) that ∀ l : ℕ

        sₗ = R (h/(2^l))

where h is some (unknown but fixed) floating point number
and

  R h = A + B * h^p₀ + C * h^p₁ + ...

with (unknown but fixed) floating point numbers
A, B, C, ... and p₀ < p₁ < p₂ < ... . We want to estimate p₀.

For any l : ℕ we have

sₗ - sₗ₊₁ =  B * h^p₀ * 2^(- p₀ * l) * (1 - 2^(-p₀)) + O (h^p₁)

and thus (up to higher order terms...)

(sₗ - sₗ₊₁) / (sₗ₊₁ - sₗ₊₂) =
2^((- p₀ * l) - (- p₀ * l - p)) = 2^p₀

So we can compute an estimate of p₀ using three consecutive
terms in our stream, e.g. s₀, s₁, s₂:
-}

approx-order : Stream Float → Float
approx-order s =
  let
    s₀ = head s
    s₁ = head (tail s)
    s₂ = head (tail (tail s))
  in
    ln 2.0 ((s₀ - s₁) / (s₁ - s₂))

{-
For the above sequences, we respectively (using "normalize"
i.e. C-c C-n) get:

approx-order archimedean-pi-sequence
1.9580817311389207

approx-order better-pi-sequence
3.979128373915537

approx-order even-better-pi-sequence
5.987692601668532

which is roughly what to expect. Note however that we
knew from our geometrical analysis that the "right"
approximation order of archimedean-pi-sequence is 2 and
used this value in the computation of better-pi-sequence...

Now it is easy to compute a stream of approximations for
the approximation order by "mapping approx-order to the
stream of tails" of our given stream: We define tails-stream
with help of the general unfold-stream
-}

unfold-stream : {A B : Set} → (A → B) → (A → A) → (A → Stream B)
head (unfold-stream h t a) = h a
tail (unfold-stream h t a) = unfold-stream h t (t a)

tails-stream : {A : Set} → Stream A → Stream (Stream A)
tails-stream = unfold-stream id tail

{-
and now map approx-order over this...
-}

approx-orders : Stream Float → Stream Float
approx-orders = (map-streams approx-order) ∘ tails-stream

{-
Try this out normalizing "take 10 (approx-orders ...-sequence)" !

While the first terms are quite good approximations, later terms
are getting less accurate or even evaluate to exceptional values
like NaN or -Infinity. This probably is because we didn't heed the
advise to avoid computing differences of nearly equal numbers :
sₗ , sₗ₊₁ , sₗ₊₂  get closer to one another with growing l.

How to avoid this ? We also have (up to higher order terms...)

(sₗ - s₀)/(sₗ₊₁ - s₁) =
B * h^p₀ * (2^(-l * p₀) - 1)  /  B * h^p₀ * 2^(-p₀) * (2^(-l * p₀) - 1)
2^p₀

-}

approx-orders'-help : Float → Float → Stream Float → Float
approx-orders'-help s₀ s₁ seq =
  let
    sₗ = head seq
    sₗ₊₁ = head (tail seq)
  in
    ln 2.0 ((sₗ - s₀) / (sₗ₊₁ - s₁))

approx-orders' : Stream Float → Stream Float
approx-orders' seq =
  let
    s₀ = head seq
    s₁ = head (tail seq)
    t = tail (tail seq)
  in
   map-streams (approx-orders'-help s₀ s₁) (tails-stream t)

{-
Ok, this doesn't give NaN, but ... these sequences of approximations
don't seem to get "better" but instead are more or less constant...

Any other ideas?

-}

----------------------
-- Richardson toolbox
----------------------

make-zeno-sequence : (Float → Float) → Float → Stream Float
head (make-zeno-sequence R h) = R h
tail (make-zeno-sequence R h) = make-zeno-sequence R (h / 2.0)


accelerate-zeno-sequence : Stream Float → Float → Stream Float
accelerate-zeno-sequence seq p = zip-streams
                               (λ rh rh/2 →  (((2.0 ^ p) * rh/2) - rh) / ((2.0 ^ p) - 1.0))
                               seq (tail seq)

make-zeno-tableau : Stream Float → Float → Float → Stream (Stream Float)
make-zeno-tableau seq p q = sequences seq p where
  sequences : Stream Float → Float → Stream (Stream Float)
  head (sequences s o) = s
  tail (sequences s o) = sequences (accelerate-zeno-sequence s o) (o + q)

-- ^^^^^^^
-- Homework for 19.12.23
-- As an exercise, also implement make-zeno-tableau using stream-of-iterations
-- by completing the following:

Stream×Order : Set
Stream×Order = Stream Float × Float

next : Float → Stream×Order → Stream×Order
next q (seq , o) = (accelerate-zeno-sequence seq o , o + q)

make-zeno-tableau' : Stream Float → Float → Float → Stream (Stream Float)
make-zeno-tableau' seq p q = map-streams proj₁ soStream where
      soStream : Stream Stream×Order
      soStream = stream-of-iterations (next q) (seq , p)

-- we complete the Richardson toolbox by:

first-term-of-zeno-tableau : Stream (Stream Float) → Stream Float
first-term-of-zeno-tableau = map-streams head

richardson-sequence : Stream Float → Float → Float → Stream Float
richardson-sequence seq p q = first-term-of-zeno-tableau (make-zeno-tableau seq p q)

close-enuf? : Float → Float → Float → Bool
close-enuf? h₁ h₂ tolerance = ∣ h₁ - h₂ ∣ ≤ 0.5 * tolerance * (∣ h₁ ∣ + ∣ h₂ ∣ + 2.0)

stream-limit : Stream Float → Float → ℕ → Float
stream-limit seq tolerance fuel = loop fuel seq where
  loop : ℕ → Stream Float → Float
  loop zero    s = head (tail s)
  loop (suc n) s =
    let
      h₁ = head s
      t  = tail s
      h₂ = head t
    in
      if (close-enuf? h₁ h₂ tolerance) then h₂ else (loop n t)

richardson-limit : (Float → Float) → Float → Float → Float → Float → ℕ → Float
richardson-limit f start-h ord inc tolerance fuel =
   stream-limit (richardson-sequence (make-zeno-sequence f start-h) ord inc) tolerance fuel
