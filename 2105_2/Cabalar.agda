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
--   defined... like in the paper, we take variables, ⊥, ∨,
--   ∧ and ⇒ as primitive, and define ¬, ⊤ and ⇔ (note that
--   we cannot use the symbols → and ≡ are, as they are used
--   for the function type and propositional equality, resp.

infixr 10 _∧_      -- \and
infixr 8 _∨_       -- \or
infixr 12 _⇒_      -- \=>
infixr 12 _⇔_      -- \<=>

data F : Set where
  V   : Var → F
  ⊥   : F               -- \bot
  _∨_ : F → F → F       -- \or
  _∧_ : F → F → F       -- \and
  _⇒_ : F → F → F       -- \=>


¬ : F → F               -- \neg
¬ f = f ⇒ ⊥

⊤ : F                   -- \top
⊤ = ¬ ⊥

_⇔_ : F → F → F
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)


-- Interpretations

IP : Set
IP = Var → 𝔹

-- Evaluation

eval : IP → F → 𝔹
eval m (V x) = m x
eval m ⊥ = false
eval m (f₁ ∧ f₂) = (eval m f₁) ∧𝔹 (eval m f₂)
eval m (f₁ ∨ f₂) = (eval m f₁) ∨𝔹 (eval m f₂)
eval m (f₁ ⇒ f₂) = ¬𝔹(eval m f₁) ∨𝔹 (eval m f₂)

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
f ∈ []       = Ø                  -- \O ... the empty theory has no elements!
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs) -- \u+ ... f is an element of a nonempty theory (g ∷ gs)
                                  --         if either f equals g or f is in gs

-- any type family on |F| (i.e. a property of fomulas) defines a type
-- family on theories

All : (F → Set) → Th → Set
All P th = (f : F) → f ∈ th → P f

-- model relation
-- we define the relation 'models' between interpretations and formulas

infix 20 _⊧_     -- \models
_⊧_ : IP → F → Set
m ⊧ f = eval m f ≡ true

-- and extend it to (finite) sets of formulas

infix 20 _⊨_     -- \|=
_⊨_ : IP → Th → Set
m ⊨ th = All (m ⊧_) th   -- (f : F) → f ∈ th → m ⊧ f  

-- models of a formula

ModF : F → Set
ModF f = Σ IP ( _⊧ f)

-- Note that |Mod f| can be considered as the type of proofs of the statement
-- "f has a model" or "there exists a model of f" or "f is satisfyable". This
-- exemplifies the use of Σ-types for existential statements.
--
-- What if we replace Σ above with Π ? Agda uses a different (and arguably more
-- informative) syntax for Π-types than for Σ-types, but to stress the analogy
-- to Σ we can easily define

Π : (A : Set) → (A → Set) → Set    -- Note that the type of Π we give here is
                                   -- (up to universe polymorphism) the same
                                   -- as the type of Σ
Π A P = (x : A) → P x

-- and then, in complete analogy to |ModF| can write

IsValidF : F → Set
IsValidF f = Π IP ( _⊧ f)

-- |IsValidF f| is the type of proofs of the statement "every |m : IP| is
-- a model of |f|", i.e. "|f| is a valid formula" or "|f| is a tautology


-- models of a theory
-- like the model relation itself, we extend |ModF| and |IsValidF| to theories:

ModTh : Th → Set
ModTh th = Σ IP ( _⊨ th )

IsValidTh : Th → Set
IsValidTh th = Π IP ( _⊨ th )


-- "Here-and-There"-Logic
--------------------------

-- interpretations for "Here-and-There" are pairs of classical
-- interpretations (deviating from the paper where these are written
-- (X,Y), we use an agda record type with constructor ► and projections
-- "Here" and "There".): 

infix 15 _►_  -- \t7

record IP-HT : Set where
  constructor
    _►_

  field
    Here : IP
    There : IP

-- model relation (just for formulas)

{- to be completed...

infix 20 _⊧HT_     -- \models
_⊧-HT_ : IP-HT → F → Set
(H ► T) ⊧-HT V x = H ⊧ V x
(H ► T) ⊧-HT ⊥ = Ø
(H ► T) ⊧-HT (f ∨ g) = {!!}
(H ► T) ⊧-HT (f ∧ g) = {!!}
(H ► T) ⊧-HT (f ⇒ g) = {!!}

-}
