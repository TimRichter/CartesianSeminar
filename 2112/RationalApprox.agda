module RationalApprox where

open import Agda.Builtin.Equality
open import Agda.Builtin.Int
open import Data.Bool
open import Data.Float renaming (_≤ᵇ_ to _≤F?_ ; _≡ᵇ_ to _≡F?_)
open import Data.List renaming (map to mapList)
open import Data.Nat renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_ ; _<ᵇ_ to _<ℕ?_)
open import Data.Maybe renaming (map to mapMb)
open import Data.Product
open import Function.Base
open import Data.Unit
open import Data.Maybe.Categorical

-- We read "Can a number be approximately rational", Chapter 1 of
-- Fuchs, Tabachnikov: "Mathematical Omnibus - Thirty lectures on classic mathematics"
-- and want to implement the "trick" described in section 1.4.

-- To keep things simple, we restrict ourselves
-- to nonnegative continued fractions.

ContFrac : Set
ContFrac = List ℕ

-- Float constants 0 an 1:

0F 1F : Float
0F = fromℕ 0
1F = fromℕ 1

-- Compute (n numbers of) the continued fraction
-- expansion of a Float α. Note that we have to return
-- a Maybe ContFrac since both the "floor" (⌊_⌋) and floating
-- point division "÷" yield only Maybe's.
-- Note furthermore that the result may be |just cf| with
-- a |cf| shorter than the given |n|, namely if in the course
-- of the recursion some "rest" (α - ⌊α⌋) is equal to 0 (in
-- the sense of ≡F?).

fromFloat : (n : ℕ) → (α : Float) → Maybe ContFrac
fromFloat zero α = just []
fromFloat (suc n) α with ⌊ α ⌋
...| nothing = nothing
...| just (negsuc _) = nothing
...| just (pos a) with (α - fromℕ a  ≡F? 0F)
...  | true = just (a ∷ [])
...  | false with (fromFloat n (1F ÷ (α - (fromℕ a))))
...    | nothing = nothing 
...    | just rest = just (a ∷ rest)

-- for the convergents we'll just use pairs of natural numbers...

ℚ : Set
ℚ = ℕ × ℕ

_⁻¹ : ℚ → ℚ
(p , q)⁻¹ = (q , p)

-- compute a float from a rational

ℚtoFloat : ℚ → Float
ℚtoFloat (p , q) = fromℕ p ÷ fromℕ q

-- expand our (finite!) continued fractions to rationals

toℚ : ContFrac → ℚ
toℚ [] = (1 , 0)
toℚ (a₀ ∷ as) =
  let
    (p' , q') = toℚ as
  in
    (a₀ *ℕ p' +ℕ q' , p')

-- we compute the convergents of a (finite) continued fraction
-- by computing the list of initial segments using |inits|
-- and then applying |mapList toℚ|

convergents : ContFrac → List ℚ
convergents = (mapList toℚ) ∘ inits

-- in a continued fraction of a Float that comes from
-- a rational (with "small" denominator), one usually
-- encounters some "big" aᵢ.  

-- This function tests for the occurence of a "big"
-- element in a ContFrac

hasGreater : ℕ → ContFrac → Bool
hasGreater _ [] = false
hasGreater n (a₀ ∷ as) with n <ℕ? a₀
... | true = true
... | false = hasGreater n as

-- This cuts the given continued fraction before the
-- first "big" element, if there is one 

cutBefore : ℕ → ContFrac → ContFrac
cutBefore bound [] = []
cutBefore bound (a₀ ∷ as) with (bound <ℕ? a₀)
...| true  = []
...| false = a₀ ∷ cutBefore bound as

-- isSmallRatio "filters" a continued fraction:
-- |isSmallRation l b cf| returns nothing if
--  - the length of cf is not smaller than l
--  - and none of the elements (a₀ , a₁, ...) of cf exceeds b
-- If |length cf| < l, just cf is returned.
-- If aᵢ is the first element bigger than b,
-- just (a₀ , ... , aᵢ₋₁) is returned.

isSmallRatio : (length : ℕ) → (elementbound : ℕ) → ContFrac → Maybe ContFrac
isSmallRatio l b cf with (length cf <ℕ? l)
... | true = just cf
... | false with (hasGreater b cf)
...   | true = just (cutBefore b cf)
...   | false = nothing

-- Kleisli composition for Maybe (using >>= -- or "bind" -- from the
-- standard lib ... I didn't find Kleisli composition there...)

_⊚_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → A → Maybe C
f ⊚ g = λ x → g x >>= f

-- Guess is a "heuristic" to decide whether the given float
-- is close to a rational number with not too large denominator.
-- It first expands the input to a ContFrac, "filters" this with
-- "isSmallRatio", and returns (just ...) the corresponding close
-- rational or |nothing| if none is found. Works quite good in
-- tests, see below.

guess : Float → Maybe ℚ
guess = (mapMb toℚ) ∘ ((isSmallRatio 15 1000) ⊚ (fromFloat 15))

-- Tests:

-- 829/911
test1 : Maybe ℚ
test1 = guess 0.90998902

-- 4/11 * sqrt 7
test2 : Maybe ℚ
test2 = guess 0.962091386

-- 311/887
test3 : Maybe ℚ
test3 = guess 0.350620067

-- random sequences (all these give "nothing")
test4 test5 test6 test7 test8 : Maybe ℚ
test4 = guess 0.531072991
test5 = guess 0.889540237
test6 = guess 0.263727532
test7 = guess 0.528768616
test8 = guess 0.136605528

-- more ratios (these give "just (717 , 775)",
-- "just (563 , 993)", etc.)
test9 test10 test11 test12 test13 : Maybe ℚ
test9  =  guess 0.925161290 -- 717/775
test10 =  guess 0.566968781 -- 563/993
test11 =  guess 0.220760233 -- 151/684
test12 =  guess 0.611374408 -- 129/211
test13 =  guess 2.664473684 -- 405/152

-- 1/π
invpi : Float
invpi = 0.318309886
-- "best" rational convergents of 1/π
invpiconv : Maybe (List ℚ)
invpiconv = mapMb convergents (fromFloat 15 invpi)
