{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Float renaming (primFloatSqrt to sqrt)
open import Data.Nat hiding (_+_;_*_)
open import Data.List hiding (head; tail; take; zip)
open import Function.Base using (_∘_)

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
flow next n = {!!}
-- flow f n   schreibt man normalerweise   f^n
-- was ist flow next 0  ?
-- wie verhält sich flow next (n + m)  zu  flow next n und flow next m ?



refine-by-doubling : Float → Float
refine-by-doubling s = s / sqrt (2.0 + sqrt (4.0 - s * s))

side-lengths : Stream Float
side-lengths = stream-of-iterations refine-by-doubling (sqrt 2.0)

side-numbers : Stream Float
side-numbers = stream-of-iterations (λ x → 2.0 * x) 4.0

semi-perimeter : Float → Float → Float
semi-perimeter length-of-side number-of-sides = (number-of-sides / 2.0) * length-of-side

zip : {A B C : Set} → (A → B → C) → Stream A → Stream B → Stream C
head (zip op as bs) = op (head as) (head bs)
tail (zip op as bs) = zip op (tail as) (tail bs)

archimedean-pi-sequence : Stream Float
archimedean-pi-sequence = zip semi-perimeter side-lengths side-numbers
