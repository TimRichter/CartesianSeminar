{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Float renaming (primFloatSqrt to sqrt)
open import Data.Nat hiding (_+_;_*_)
open import Data.List hiding (head; tail; take; zip)
open import Function.Base using (_∘_ ; id; flip)

module HalfantSussman where

infixl 20 _+_
infixl 20 _-_
infixl 21 _*_
infixl 19 _/_

_+_ _-_ _*_ _/_ : Float → Float → Float
_+_ = primFloatPlus
_-_ = primFloatMinus
_*_ = primFloatTimes
_/_ = primFloatDiv

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream public


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
flow next zero = λ a → a
flow next (suc n) = λ a → (next (flow next n a))

-- e.g. compute flow next 2:
-- flow next (suc (suc zero)) a = next (flow next (suc zero) a)
--                              = next (next (flow next zero a))
--                              = next (next (a))
-- i.e. flow next 2 is (extensionally) equal to   next ∘ next

-- Tim: when I gave the exercise, I had in mind:
-- ℕ → A    and    Stream A   are  "the same" (isomorphic,
-- in bijection, equivalent) via the functions fun2Stream and _!!_
-- and flow is nothing else than  stream-of-iterations transported
-- along this equivalence ... What I missed was: stream-of-iterations f
-- isn't a stream but of type  A → Stream A ...
-- So we have to postcompose with _!!_ to get someting of
-- type  A → ℕ → A, and flip this binary function to get the flow:

flow' : {A : Set} → (A → A) → ℕ → A → A
flow' = flip ∘ (_!!_ ∘_) ∘ stream-of-iterations

-- flow f n  is usually writte   f^n
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

-- already the 6th term of even-better-pi-sequence has
-- 15 digits of π correct.  However, after that it doesn't
-- get better and instead ocillates... to be discussed.
