module Cabalar where

-- formalizing some aspects of Pedro Cabalar's and Paolo Ferraris' 2007 paper
-- "Propositional Theories are Strongly Equivalent to Logic Programs"

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _∧_ to _∧𝔹_ ; _∨_ to _∨𝔹_ ; not to ¬𝔹)
open import Data.List using (List ; _∷_ ; [])
open import Data.Empty renaming (⊥ to ∅ ; ⊥-elim to ∅-elim )  -- \0
open import Data.Sum.Base using ( _⊎_ ) renaming ( inj₁ to inl ; inj₂ to inr )
open import Data.Product using ( _×_ ; _,_ ) renaming (proj₁ to p1 ; proj₂ to p2)

-- Preliminaries: Some concepts of (classical) propositional logic
------------------------

-- some properties of ≡

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

symm  : {A : Set} → {x y : A} → x ≡ y → y ≡ x
symm refl = refl

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
f ∈ []       = ∅                  -- \0 ... the empty theory has no elements!
f ∈ (g ∷ gs) = (f ≡ g) ⊎ (f ∈ gs) -- \u+ ... f is an element of a nonempty theory (g ∷ gs)
                                  --         if either f equals g or f is in gs

-- any type family on |F| (i.e. a property of fomulas) defines a type
-- family on theories

All : (F → Set) → Th → Set
All P th = (f : F) → f ∈ th → P f

-- model relation
-- we define the relation 'models' between interpretations and formulas

-- a nice and short definition uses the eval function

infix 20 _⊧ev_     -- \models
_⊧ev_ : IP → F → Set
m ⊧ev f = eval m f ≡ true

-- however, |m ⊧ev f| does not contain any information
-- other than "|f| evaluates to true under interpretation |m|".
-- But in proofs that proceed by formula structure, one often
-- needs to know that, e.g. |m ⊧ f ∧ g| holds iff |m ⊧ f| and |m ⊧ g|.
-- We therefore give another definition and then show that both
-- are (logically) equivalent, i.e. that we have mappings from
-- one to the other and back.

infix 20 _⊧_     -- \models
_⊧_ : IP → F → Set
m ⊧ V x = m x ≡ true
m ⊧ ⊥ = ∅
m ⊧ (f ∨ g) = m ⊧ f ⊎ m ⊧ g
m ⊧ (f ∧ g) = m ⊧ f × m ⊧ g
m ⊧ (f ⇒ g) =  m ⊧ f → m ⊧ g

-- Lemmata on equality in 𝔹:

dec𝔹 : (a : 𝔹) → (a ≡ true ⊎ a ≡ false)
dec𝔹 false = inr refl
dec𝔹 true = inl refl

trueIsNotFalse : true ≡ false → ∅
trueIsNotFalse ()

-- contraposition (kind of)

contra : (a b : 𝔹) → ((a ≡ true) → (b ≡ true)) → ((b ≡ false) → (a ≡ false))
contra a b a2b bfalse with (dec𝔹 a)
... | inr refl = refl
... | inl refl with b
...    | false = symm (a2b refl)
...    | true  = bfalse

∨𝔹to : {a b : 𝔹} → ( a ≡ true ⊎ b ≡ true ) → a ∨𝔹 b ≡ true
∨𝔹to {a = true}             (inl x) = refl
∨𝔹to {a = false} {b = true} (inr y) = refl
∨𝔹to {a = true}  {b = true} (inr y) = refl
-- all these cases are needed...!

∨𝔹from : {a b : 𝔹} → a ∨𝔹 b ≡ true → (a ≡ true ⊎ b ≡ true)
∨𝔹from {a = false} {b = true} _ = inr refl
∨𝔹from {a = true}             _ = inl refl

∧𝔹to : {a b : 𝔹} → ( a ≡ true × b ≡ true ) → a ∧𝔹 b ≡ true
∧𝔹to {a = true} {b = true} _ = refl

∧𝔹from : {a b : 𝔹} → a ∧𝔹 b ≡ true → ( a ≡ true × b ≡ true )
∧𝔹from {a = true} {b = true} _ = ( refl , refl )

infix 12 _⇒𝔹_

_⇒𝔹_ : 𝔹 → 𝔹 → 𝔹
a ⇒𝔹 b = ¬𝔹 a ∨𝔹 b

⇒𝔹to : {a b : 𝔹} → ( a ≡ true → b ≡ true ) → a ⇒𝔹 b ≡ true
⇒𝔹to {a = false} f = refl
⇒𝔹to {a = true}  f = f refl

⇒𝔹from : {a b : 𝔹} → a ⇒𝔹 b ≡ true → ( a ≡ true → b ≡ true )
⇒𝔹from {a = false} {b = false} _ q = q
⇒𝔹from {a = true } {b = false} p _ = p
⇒𝔹from {a = true } {b = true } _ _ = refl 
⇒𝔹from {a = false} {b = true } _ _ = refl

-- here's yet another subtle reformulation of | a ⇒𝔹 b ≡ true |

⇒𝔹to' : {a b : 𝔹} → a ≡ false ⊎ b ≡ true → a ⇒𝔹 b ≡ true
⇒𝔹to' {a = false}              _                = refl 
⇒𝔹to' {a = true } {b = false} (inr falseIsTrue) = falseIsTrue
⇒𝔹to' {a = true } {b = true }  _                = refl

⇒𝔹from' : {a b : 𝔹} → a ⇒𝔹 b ≡ true → a ≡ false ⊎ b ≡ true
⇒𝔹from' {a = false} {b = false} _ = inl refl
⇒𝔹from' {a = false} {b = true } _ = inr refl  -- there is  choice here... could also take |inl refl|
⇒𝔹from' {a = true } {b = true } _ = inr refl


-- note that the following two functions, implementing the
-- equivalence between ⊧ and ⊧ev, use mutual induction!

mod2modev : {m : IP} → {f : F} → m ⊧ f → m ⊧ev f
modev2mod : {m : IP} → {f : F} → m ⊧ev f → m ⊧ f

mod2modev {m} {V x}    m⊧         = m⊧
mod2modev {m} {f ∨ g} (inl m⊧f)   = ∨𝔹to (inl (mod2modev m⊧f))
mod2modev {m} {f ∨ g} (inr m⊧g)   = ∨𝔹to (inr (mod2modev m⊧g))
mod2modev {m} {f ∧ g} (m⊧f , m⊧g) = ∧𝔹to ( mod2modev m⊧f , mod2modev m⊧g )
mod2modev {m} {f ⇒ g}  m⊧         = ⇒𝔹to λ m⊧evf → mod2modev (m⊧ (modev2mod m⊧evf))

modev2mod {m} {V x} p   = p
modev2mod {m} {f ∨ g} p with (∨𝔹from p)
... | inl m⊧evf = inl (modev2mod m⊧evf)
... | inr m⊧evg = inr (modev2mod m⊧evg)
modev2mod {m} {f ∧ g} p = ( modev2mod (p1 (∧𝔹from p)) , modev2mod (p2 (∧𝔹from p)) )
modev2mod {m} {f ⇒ g} p m⊧f = modev2mod (⇒𝔹from p (mod2modev m⊧f))

-- extend ⊧ to (finite) sets of formulas

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

infix 30 _►_  -- \t7

record IP-HT : Set where
  constructor
    _►_

  field
    Here : IP
    There : IP

-- model relation (just for formulas)
-- Note how the metalogical junctors "and", "or" and "implies" used
-- in the paper are modeled by the type constructors "×", "⊎", "⇒" !

infix 20 _⊧-HT_     -- \models
_⊧-HT_ : IP-HT → F → Set
H ► T ⊧-HT V x = H ⊧ V x
H ► T ⊧-HT ⊥ = ∅
H ► T ⊧-HT (f ∨ g) = (H ► T ⊧-HT f) ⊎ (H ► T ⊧-HT g)
H ► T ⊧-HT (f ∧ g) = (H ► T ⊧-HT f) × (H ► T ⊧-HT g)
H ► T ⊧-HT (f ⇒ g) = ((H ► T ⊧-HT f) → (H ► T ⊧-HT g)) × T ⊧ (f ⇒ g)

-- The rule for implication is the only one referring to T.
-- If we modify ⊧-HT by dropping the (T ⊧ (f ⇒ g)) part of the
-- implication rule

infix 20 _⊧-HT'_     -- \models
_⊧-HT'_ : IP-HT → F → Set
H ► T ⊧-HT' V x = H ⊧ V x
H ► T ⊧-HT' ⊥ = ∅
H ► T ⊧-HT' (f ∨ g) = (H ► T ⊧-HT' f) ⊎ (H ► T ⊧-HT' g)
H ► T ⊧-HT' (f ∧ g) = (H ► T ⊧-HT' f) × (H ► T ⊧-HT' g)
H ► T ⊧-HT' (f ⇒ g) = (H ► T ⊧-HT' f) → (H ► T ⊧-HT' g)

-- we can prove 

HtoHT' : {H T : IP} → {f : F} → (H ⊧ f) → (H ► T ⊧-HT' f)
HT'toH : {H T : IP} → {f : F} → (H ► T ⊧-HT' f) → (H ⊧ f)
HtoHT' {H} {T} {V x} ⊧Vx = ⊧Vx
HtoHT' {H} {T} {f ∨ g} (inl ⊧f) = inl (HtoHT' ⊧f)
HtoHT' {H} {T} {f ∨ g} (inr ⊧g) = inr (HtoHT' ⊧g)
HtoHT' {H} {T} {f ∧ g} (⊧f , ⊧g)  = (HtoHT' ⊧f , HtoHT' ⊧g)
HtoHT' {H} {T} {f ⇒ g} ⊧ftog = λ ⊧'f → HtoHT' (⊧ftog (HT'toH ⊧'f))

HT'toH {f = V x} HT⊧'Vx = HT⊧'Vx
HT'toH {f = f ∨ g} (inl ⊧'f) = inl (HT'toH ⊧'f)
HT'toH {f = f ∨ g} (inr ⊧'g) = inr (HT'toH ⊧'g)
HT'toH {f = f ∧ g} (⊧'f , ⊧'g ) = (HT'toH ⊧'f , HT'toH ⊧'g)
HT'toH {f = f ⇒ g} p = λ ⊧f → HT'toH (p (HtoHT' ⊧f))
