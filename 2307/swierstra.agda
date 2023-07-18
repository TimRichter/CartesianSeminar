module swierstra {A : Set} where

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
elemtest1 = First
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

data _+_ (C D : Set) : Set where
  inl : C → C + D
  inr : D → C + D

data False : Set where

isDec : Set → Set
isDec B = B + (B → False)

hasDecEq : Set → Set
hasDecEq C = ∀ (c₁ c₂ : C) → isDec (c₁ ≡ c₂) 

checkElem : {B : Set} → {hasDecEq B} → B → List B → Bool
checkElem {B} {deq} x [] = false
checkElem {B} {deq} x (y :: ys) with (deq x y)
... | inl _ = true
... | inr _ = checkElem {B} {deq} x ys


data Ref : U → Ctx → Set where
  Top : {σ : U} → {Γ : Ctx} → Ref σ (σ :: Γ)
  Pop : {σ τ : U} → {Γ : Ctx} → Ref σ (τ :: Γ)

{- could have |σ| as a parameter (instead of an index) to
   shorten a little:

data Ref (σ : U) : Ctx → Set where
  Top : {Γ : Ctx} → Ref σ (σ :: Γ)
  Pop : {τ : U} → {Γ : Ctx} → Ref σ (τ :: Γ)

  However, |τ| and |Γ| have to be indices!
-}
