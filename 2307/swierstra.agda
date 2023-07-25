module swierstra where

postulate
  A : Set

infix 15 _⇒_

data U : Set where
 ι : U
 _⇒_ : U → U → U

Val : U → Set
Val ι = A
Val (u₁ ⇒ u₂) = Val u₁ → Val u₂

infixr 20 _::_

data List (B : Set) : Set where
 [] : List B
 _::_ : B → List B → List B

Ctx : Set
Ctx = List U

-- Exkurs: Ref below is similar to the type (family)

data Elem {B : Set} : B  → List B → Set where
 First :  {b : B} → {bs : List B} →  Elem b (b :: bs)
 Later :  {b b' : B} → {bs : List B} → Elem b bs → Elem b (b' :: bs)

-- For any type |B|, element |b : B| and list |bs : List B|, the
-- elements of |Elem b bs| are proofs of the statement "b occurs in bs".
-- E.g., taking Bool for B,

data Bool : Set where
 true : Bool
 false : Bool

-- here are two proofs that |True| is an element of the list |True :: False :: True :: []|  :

elemtest1 elemtest2 : Elem true (true :: false :: true :: [])
elemtest1 = First               -- First {true} {false :: true :: []}
elemtest2 = Later (Later First)

-- Why do we define this rather complicated type? Couldn't we just implement a function
-- checkElem : {B : Set} → B → List B → Bool      ?
-- No! To implement checkElem, we need to require B to have decidable equality
-- and there are a lot of types (i.e. |ℕ → Bool|) that do not have a
-- decidable equality...!

if_then_else_ : {B : Set} → Bool → B → B → B
if true then t else f = t
if false then t else f = f

data _≡_ {B : Set} (b : B) : B → Set where
  refl : b ≡ b

data _+_ (C D : Set) : Set where   -- Either , _∨_
  inl : C → C + D
  inr : D → C + D

data False : Set where

infixr 20 ⟨_,_⟩

data _×_ (C D : Set) : Set where
  ⟨_,_⟩ : C → D → C × D

fst : {C D : Set} → C × D → C
fst ⟨ x , _ ⟩ = x

isDec : Set → Set           -- "B is decidable"
isDec B = B + (B → False)   -- "(to) B or not (to) B"

hasDecEq : Set → Set
hasDecEq C = (c₁ c₂ : C) → isDec (c₁ ≡ c₂)

checkElem : {B : Set} → {hasDecEq B} → B → List B → Bool
checkElem {B} {deq} x [] = false
checkElem {B} {deq} x (y :: ys) with (deq x y)
... | inl _ = true
... | inr _ = checkElem {B} {deq} x ys

-- in Haskell we have type class Eq. B is in this typeclass
-- if there is a function _==_ : B → B → Bool.
-- Given such a function, we can implement

checkElemByEq : {B : Set} → (B → B → Bool) → B → List B → Bool
checkElemByEq beq b [] = false
checkElemByEq beq b (b' :: bs) with (beq b b')
... | true  = true
... | false = checkElemByEq beq b bs

-- but the boolean predicate beq might be anything and does
-- not need to be any kind of equality...

-- But if we have |hasDecEq B|, we can produce a "trustable"
-- boolean equality check.

checkEq : {B : Set} → {hasDecEq B} → B → B → Bool
checkEq {B} {deq} x y with (deq x y)
... | inl _ = true
... | inr _ = false

-- We could have defined checkElem as

checkElem' : {B : Set} → {hasDecEq B} → B → List B → Bool
checkElem' {B} {deq} = checkElemByEq (checkEq {B} {deq})



data Ref : U → Ctx → Set where
  Top : {σ : U}   → {Γ : Ctx} → Ref σ (σ :: Γ)
  Pop : {σ τ : U} → {Γ : Ctx} → Ref σ (τ :: Γ)

{- could have |σ| as a parameter (instead of an index) to
   shorten a little:

data Ref (σ : U) : Ctx → Set where
  Top : {Γ : Ctx} → Ref σ (σ :: Γ)
  Pop : {τ : U} → {Γ : Ctx} → Ref σ (τ :: Γ)

  However, |τ| and |Γ| have to be indices!
-}

-- ≤  on natural numbers

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

natAdd : ℕ → ℕ → ℕ
natAdd  Z    y = y
natAdd (S x) y = S (natAdd x y)

{- Nicola: Bertrand Meyer (Eiffel-Autor) in "OOSC":
   "Cosmetics matter!"
   insbesondere Namensgebung
-}

_+ℕ_ : ℕ → ℕ → ℕ
Z  +ℕ  y = y
(S x) +ℕ y = S (natAdd x y)


-- Julian:
_≤B_ : ℕ → ℕ → Bool
Z   ≤B n = true
S m ≤B Z = false
S m ≤B S n = m ≤B n

data True : Set where
  * : True

-- Marcus:
_≤S_ : ℕ → ℕ → Set
Z ≤S n     = True -- could be any type but False!
S m ≤S Z   = False
S m ≤S S n = m ≤S n

gugu : 0 ≤S 1
gugu = *

gugu' : 0 ≤S 5
gugu' = *

lala : 1 ≤S 0
lala = {!!}  -- not implementable

notLala : 1 ≤S 0 → False
notLala = λ x → x
-- or via absurd pattern (ex falso quodlibet)
-- notLala ()

gaga : 1 ≤S 3
gaga = gugu

-- Bastian:
_≤N_ : ℕ → ℕ → ℕ
m ≤N n = {!!}


-- Nicola:
data _≤D_ : ℕ → ℕ → Set where
  ZLess : {m : ℕ} → 0 ≤D m
  SLess : {m n : ℕ} → m ≤D n → S m ≤D S n

tata : 1 ≤D 17
tata = SLess ZLess

{-
-- Bastian:
data _≤D_ : ℕ → ℕ → Set where
  EQ : {m : ℕ} → m ≤D m
  OneLess : {m : ℕ} → m ≤D S m
  ChainLess : {m n o : ℕ} →
              m ≤D n → n ≤D o → m ≤D o

tata : 0 ≤D 3
tata = ChainLess OneLess (ChainLess OneLess OneLess)
-}

{-
-- Conor
data _≤C_ : ℕ → ℕ → Set where
  Base : 0 ≤C 0
  Skip : {m n : ℕ} → m ≤C n → S m ≤C S n
  Take : {m n : ℕ} → m ≤C n → m ≤C S n

tata' : 2 ≤C 4
tata' = Skip (Take (Skip (Take Base)))
-}
