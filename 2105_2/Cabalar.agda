module Cabalar where

-- formalizing some aspects of Pedro Cabalar's and Paolo Ferraris' 2007 paper
-- "Propositional Theories are Strongly Equivalent to Logic Programs"

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to Ø ; ⊥-elim to Ø-elim )
open import Data.Sum.Base using ( _⊎_ )

-- Preliminaries: Some concepts of (classical) propositional logic
------------------------

-- Variables (countably many, indexed by ℕ)

data Var : Set where   -- note that "Set" is Agda jargon for "Universe" or "Type".
  X : ℕ → Var          -- As in the HoTT book, in Agda there are "universe levels",
                       -- Set₀ , Set₁ , Set₂ , ... We only need "Set₀", for which
                       -- there is the notation "Set". 

-- Propositional Formulas
--   it is not soo important which operations are taken as
--   basic, i.e. occur as constructors in F. Others can be
--   defined (e.g. implication, see below).

infixr 10 _∧_      -- \and
infixr 8 _∨_       -- \or

data F : Set where
  V   : Var → F
  _∧_ : F → F → F
  _∨_ : F → F → F
  ¬   : F → F      -- \neg

-- (classical!) implication can be defined... (the _→_ symbol is taken...)

infixr 12 _⇒_      -- \=>

_⇒_ : F → F → F
p ⇒ c = (¬ p) ∨ p

-- Interpretations

IP : Set
IP = Var → 𝔹

-- Evaluation

eval : IP → F → 𝔹
eval m (V x) = m x
eval m (f₁ ∧ f₂) = (eval m f₁) ∧𝔹 (eval m f₂)
eval m (f₁ ∨ f₂) = (eval m f₁) ∨𝔹 (eval m f₂)
eval m (¬ f) = ¬𝔹 (eval m f)

-- A theory is a subset of formulas.
-- We restrict here to finite sets of formulas and
-- represent these by lists.

Th : Set
Th = List F

-- Here is a type that expresses the "element" relation.
-- We define it by pattern matching on the second argument,
-- which is of type List F : For any formula f
-- - there are no proofs for f ∈ []
-- - f is an element of (g ∷ gs) if either f is equal to g or
--   f is an element of gs

infix 15 _∈_

_∈_ : F → Th → Set
f ∈ []       = Ø                  -- the empty type ( \O ) ... the empty theory has no elements!
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs) -- disjoint union ( \u+ ) ... f is an element of a nonempty theory (g ∷ gs)
                                  --                            if either f equals g or f is in gs

-- model relation

infix 20 _⊧_     -- \models
_⊧_ : IP → Th → Set
m ⊧ th = (f : F) → f ∈ th → eval m f ≡ true

-- models of a theory

Mod : Th → Set
Mod th = Σ IP ( _⊧ th )
-- Note that |Mod th| can be considered as the type of proofs of the statement "th has a model" or "there exists a model of th".
-- This exemplifies the use of Σ-types for existence statements.
--
-- One also calls a formula |f| "satisfyable" if the theory | f ∷ [] | has a model. Thus, in this case, |Mod (f ∷ [])| is the type
-- of proofs of the statement "|f| is satisfyable".
--
-- What if we replace Σ above with Π ? Agda uses a different syntax for Π-types, but we can easily define

Π : (A : Set) → (A → Set) → Set
Π A P = (x : A) → P x

-- Completely analoguous to |Mod| we can now define

IsValid : Th → Set
IsValid th = Π IP ( _⊧ th )
-- |IsValid th| is the type of proofs of the statement "every |m : IP| is a model of |th|".
--
-- If |th| is a singleton list, i.e. contains exactly one formula |f|, |Π IP ( _⊧ (f ∷ []) )| is
-- the type of proofs of the statement "|f| is valid" or "|f| is a tautology".
