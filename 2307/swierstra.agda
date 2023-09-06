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
  Pop : {σ τ : U} → {Γ : Ctx} → Ref σ Γ → Ref σ (τ :: Γ)

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

ref2ℕ : ∀ {σ} {Γ} → Ref σ Γ → ℕ
ref2ℕ Top = Z
ref2ℕ (Pop x) = S (ref2ℕ x)

data Term (Γ : Ctx) : U → Set where
  App : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  Lam : ∀ {σ τ} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  Var : ∀ {σ}   → Ref σ Γ → Term Γ σ

{- interestingly, Γ above can be a parameter (doesn't have to
   be an index) -}

{- ************  examples -}

{- x -}
x : Term ((ι ⇒ ι) :: ι :: []) ι
x = Var (Pop Top)

{-   - λ x . x
   + : N -> N -> N  -}
id : ∀ {Γ} {σ} → Term Γ (σ ⇒ σ)
id = Lam (Var Top)

{- constant function  λ x . y -}

{- not so easy...
   need ins... functions to insert types somewhere
   in a context Γ (there are S (length Γ) possible positions !)
   and "lift" references and terms over Γ to a thus extended context...
-}

data Fin : ℕ → Set where
  FZ : ∀ {n} → Fin (S n)
  FS : ∀ {n} → Fin n → Fin (S n)

length : ∀ {B} → List B → ℕ
length [] = Z
length (b :: bs) = S (length bs)

insList : ∀ {B} → (bs : List B) → Fin (S (length bs)) → B → List B
insList bs FZ b'            = b' :: bs
insList (b :: bs) (FS i) b' = b :: insList bs i b'

insRef : ∀ {Γ σ τ} → (i : Fin (S (length Γ))) → Ref τ Γ → Ref τ (insList Γ i σ)
insRef FZ r           = Pop r
insRef (FS i) Top     = Top
insRef (FS i) (Pop r) = Pop (insRef i r)

insTerm : ∀ {Γ} {τ} → (σ : U) → (i : Fin (S (length Γ))) →
          Term Γ τ → Term (insList Γ i σ) τ
insTerm σ i (App t₁ t₂)        = App (insTerm σ i t₁) (insTerm σ i t₂)
insTerm σ i (Lam t)            = Lam (insTerm σ (FS i) t)
insTerm σ FZ (Var r)           = Var (Pop r)
insTerm σ (FS i) (Var Top)     = Var Top
insTerm σ (FS i) (Var (Pop x)) = Var (Pop (insRef i x))

const : ∀ {Γ} {τ σ} → Term Γ σ → Term Γ (τ ⇒ σ)
const {τ = τ} y = Lam (insTerm τ FZ y)

{- on the other hand, if we model y as a (free) variable,
   it is of course easier ... and probably more appropriate -}

one : ∀ τ σ → Term (τ :: σ :: []) τ
one τ σ = Var Top

two : ∀ τ σ → Term (τ :: σ :: []) σ
two τ σ = Var (Pop Top)

const' : ∀ τ σ → Term (σ :: []) (τ ⇒ σ)
const' τ σ = Lam (two τ σ) 

{- How does const relate to const' ?
   const {τ} {sigma} : Term Γ σ → Term Γ (τ ⇒ σ)
   describes something like evaluating const' τ σ
   in an environment where its free variable is
   instantiated with something of type Term Γ σ
   (?)
-}

{- f x  -}

app1 : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
app1 = App

{-    again, this might be more appropriate: -}

fx : ∀ τ σ → Term (σ :: (σ ⇒ τ) :: []) τ
fx τ σ = App (two σ (σ ⇒ τ)) (one σ (σ ⇒ τ))

{-   - λ x . (f x)  -}

app : ∀ {Γ σ τ} → Term Γ (σ ⇒ τ) → Term Γ (σ ⇒ τ)
app {σ = σ} f = Lam (App (insTerm σ FZ f) (Var Top))

{-      or, more appropriate... -}

app' : ∀ τ σ → Term ((σ ⇒ τ) :: []) (σ ⇒ τ)
app' τ σ = Lam (fx τ σ)

{-  - λ f . f x
      here we cannot use fx
      but have to bring the function type (σ ⇒ τ)
      to the head of the context, then we can use Lam...
-}

fx' : ∀ τ σ → Term ((σ ⇒ τ) :: σ :: []) τ
fx' τ σ = App (one (σ ⇒ τ) σ) (two (σ ⇒ τ) σ)

evalAt : ∀ τ σ → Term (σ :: []) ((σ ⇒ τ) ⇒ τ)
evalAt τ σ = Lam (fx' τ σ)

{- Nicola suggested the following variants for
   x, f, f x, λ x . x, λ x. f x und λ x . y
   in arbitrary contexts that provide references
   of appropriate types... -}

-- x
xN : ∀ {Γ σ} → Ref σ Γ → Term Γ σ
xN = Var

-- f
fN : ∀ {Γ σ τ} → Ref (σ ⇒ τ) Γ → Term Γ (σ ⇒ τ)
fN = Var

-- f x
fxN : ∀ {Γ σ τ} → Ref (σ ⇒ τ) Γ → Ref σ Γ → Term Γ τ
fxN p q = App (Var p) (Var q) 

-- λ x . x
idN : ∀ {Γ} {σ} → Ref σ Γ → Term Γ (σ ⇒ σ)
idN p = Lam (Var (Pop p))

-- λ x . f x
λfxN : ∀ {Γ σ τ} → Ref (σ ⇒ τ) Γ → Term Γ (σ ⇒ τ)
-- Nicola simply put's "f" hier, i.e.
-- λfxN = Var
-- but I think this is better:
λfxN q = Lam (App (Var (Pop q)) (Var Top))

-- λ x . y  (a.k.a. const)
constN : ∀ {Γ} {σ τ} → Ref τ Γ →  Term Γ (σ ⇒ τ)
constN q = Lam (Var (Pop q))
