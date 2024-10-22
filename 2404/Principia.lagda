Cartesisches Seminar April 2024
We read chpt.2 ("Type Theory in Principia Mathematica") of
Kamareddine, Laan, Nederpelt: "A Modern Perspective on Type Theory: From its Origins until Today"

Useful links:
- PM I https://archive.org/details/alfred-north-whitehead-bertrand-russel-principia-mathematica.-1/Alfred%20North%20Whitehead%2C%20Bertrand%20Russel%20-%20Principia%20Mathematica.%201/page/n9/mode/2up
- PM II https://archive.org/details/PrincipiaMathematicaVol2/mode/2up
- PM III https://archive.org/details/PrincipiaMathematicaVol3
- SEP on PM (by Linsky, Bernard and Irvine, Andrew David ) : https://plato.stanford.edu/entries/principia-mathematica/


Sebastian zum Buch:
- Typen in Mathematik immer schon implizit benutzt, Beispiel Punkte/Linien in Euklids Elementen
  Nicola: aber nicht dependent types, oft keine Unterscheidung totale/partielle Funktionen
  Georg: ...
  Nicola: Unterschied Paradoxien (Achilles und die Schildkröte) und echten Antinomien (Russell!)
- Paradoxien können entstehen, wenn Intuition versagt, z.B. bei
  - sehr komplexen Systemen
  - hoher Abstraktionsgrad
  - wenn Maschinen (Computer) "verstehen" sollen (haben keine Intuition)
  Nicola: Typentheorie ursprünglich zur Vermeidung von Widersprüchen in Grundlagentheorie (Set theory,
  Hilbert program) , heutige Benutzung zur Erhöhung der Softwaresicherheit etwas orthogonal dazu
- Frege wird zitiert. Relevante Werke: "Begriffsschrift", "Grundlagen der Arithmetik", "Grundgesetze der Arithmetik"
  Logizismus: ganze Mathematik auf Logik gründen

\begin{code}
open import Data.Nat hiding (_+_)
open import Data.List
open import Data.Bool hiding (_∨_; _∧_)
open import Agda.Builtin.Equality
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Function.Base
open import Relation.Binary.PropositionalEquality as P
  using (refl;cong;subst)
module Principia
\end{code}

The text starts on p 22 with the definition of the notion of a "propositional function" in
Principia Mathematica (PM):

⟫ By a "propositional function" we mean something which contains a variable x, and expresses
  a propostion as soon as a value is assigned to x. ⟪

\begin{code}
  (A : Set)            -- set(type) of individual sysmbols
  (V : Set)            -- set(type) of variables
  (R : Set)            -- set(type) of relation symbols
  (arity : R → ℕ)          -- arity
  -- alternative (relsyms : ℕ → Set)
  -- " R = Σ ℕ relsyms "  und " a = proj₁ "

  (_<_ : V → V → Set)   -- variables are ordered
  (PV : Set)            -- we postulate a type of sets of variables
  (_∈_ : V → PV → Set)  -- with a membership predicate
  (⟪_⟫ : List V → PV)   -- with a function from lists of variables
                        -- (in particular, ∅ = ⟪[]⟫, {a} = ⟪a :: []⟫, a.s.o.
  (_∪_ : PV → PV → PV)  -- featuring a union,
  (_∩_ : PV → PV → PV)  -- an intersection, and
  (_-_ : PV → PV → PV)  -- a "set minus" operation.
  -- We also postulate commutativity and idempotence of ∪:
  (comm∪ : (A B : PV) → A ∪ B ≡ B ∪ A)
  (idem∪ : (A : PV) → A ∪ A ≡ A)
  where

  -- some notation for equational reasoning
  trans≡ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans≡ refl refl = refl

  symm≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
  symm≡ refl = refl

  infixr 10 _≡⟨_⟩_   -- emacs agda-mode: \langle \rangle or \<  \>
  infixr 10 _≡⟨˘_⟩_  -- ˘ \u{}
  infixr 10 _≡⟨⟩_

  _≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y z : A} →
           x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans≡ p q

  _≡⟨˘_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y z : A} →
            y ≡ x → y ≡ z → x ≡ z
  x ≡⟨˘ p ⟩ q = trans≡ (symm≡ p) q

  _≡⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y : A} →
          x ≡ y → x ≡ y
  x ≡⟨⟩ q = x ≡⟨ refl ⟩ q

  _QED : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
  x QED = refl

  -- as a warm-up : atomic propositions

  data AtomicProp : Set where
    MkAtomicProp : (r : R) → (args : List A) → (length args ≡ arity r) → AtomicProp
    -- alternativ Lala :
    --   {n : ℕ} → relsyms n → Vect A n → AtomicProp

  ArityEq#Args : {X : Set} → R × (List X) → Set
  ArityEq#Args (r , args) = arity r ≡ length args

  AtomicProp' : Set
  AtomicProp' -- = Σ R (λ r → Σ (List A) (λ args → a r ≡ length args))
              -- = Σ (R × (List A)) (λ (r , args) → a r ≡ length args)
              = Σ (R × (List A)) ArityEq#Args

  -- now towards the type of propositional functions (Definition 2.3 in the book)

  -- We need the disjoint union type (a.k.a. Either, a.k.a. Or)
  infixr 18 _+_
  data _+_ (X Y : Set) : Set where
    inl :  X → X + Y
    inr :  Y → X + Y

  -- Here is the standard fold (a.k.a. recursor, a.k.a. non-dependent eliminator ...) of this type
  fold+ : {X Y Z : Set} → (X → Z) → (Y → Z) → X + Y → Z
  fold+ xToz yToz (inl x) = xToz x
  fold+ xToz yToz (inr y) = yToz y

  -- We use fold+ to define functions from X + Y to Maybe X resp. Maybe Y
  toMaybeL : {X Y : Set} → X + Y → Maybe X
  toMaybeL = fold+ just (const nothing)
  toMaybeR : {X Y : Set} → X + Y → Maybe Y
  toMaybeR = fold+ (const nothing) just

  toVs : List ( A + V ) → List V
  toVs = mapMaybe toMaybeR
  {-
  -- we could have defined this explicitely by
  toVs []         = []
  toVs (inl a ∷ avs) = toVs avs
  toVs (inr v ∷ avs) = v ∷ (toVs avs)
  -- but here we use the function mapMaybe from the standard library (Data.List.Base)
  mapMaybe : (A → Maybe B) → List A → List B
  mapMaybe p []       = []
  mapMaybe p (x ∷ xs) with p x
  ... | just y  = y ∷ mapMaybe p xs
  ... | nothing =     mapMaybe p xs
  -}

  -- here is a list membership predicate
  _∈L_ : {A : Set} → A → List A → Set
  x ∈L [] = ⊥
  x ∈L (a ∷ as) = (x ≡ a) + (x ∈L as)

{- variant (isomorphic to the other one)
  data _∈L'_ {A : Set} : A → List A → Set where
    Here  : (x : A) → (as : List A) → x ∈L' (x ∷ as)
    There : (x a : A) → (as : List A) → x ∈L' as → x ∈L' (a ∷ as)
-}

  fakt : 2 ∈L (2 ∷ 3 ∷ 4 ∷ [])
  fakt = inl refl

  -- Of course, we want the set we get from a list via ⟪_⟫
  -- to contain the list's elements.

  postulate
    ∈L⇒∈ : {v : V} → {vs : List V} →
             v ∈L vs → v ∈ ⟪ vs ⟫

  -- the type of propositional functions is defined mutually with the function FreeVars
  mutual
    data 𝒫ℱ : Set where
      ATOM   : (r : R) → (args : List (A + V)) → arity r ≡ length args → 𝒫ℱ
      OR     : 𝒫ℱ → 𝒫ℱ → 𝒫ℱ
      NOT    : 𝒫ℱ → 𝒫ℱ
      FORALL : (f : 𝒫ℱ) → (x : V) → x ∈ (FreeVars f) → 𝒫ℱ
      -- Z      : List (A + V + 𝒫ℱ) → 𝒫ℱ
      LALA      : V → List (A + V + 𝒫ℱ) → 𝒫ℱ

    FreeVars : 𝒫ℱ → PV
    FreeVars (ATOM r avs x)     = ⟪ toVs avs ⟫
    FreeVars (OR f g)           = (FreeVars f) ∪ (FreeVars g)
    FreeVars (NOT f)            = FreeVars f
    FreeVars (FORALL f x x∈FVf) = FreeVars f - ⟪ x ∷ [] ⟫
    FreeVars (LALA z avps)      --= ⟪ toVs' ((inr (inl z)) ∷ avps) ⟫
                                = ⟪ z ∷ [] ⟫ ∪ ⟪ toVs' avps ⟫
    {- hatten vorher Konstruktor Z und
        FreeVars (Z avps)         = ⟪ toVs' avps ⟫
        1. bei uns Z Konstruktor, kann also keine freie Variable sein
        2. Hier die einzige Stelle, wo 𝒫ℱ's vorkommen (nämlich in der Liste avps), aber FreeVars nicht rekursiv aufgerufen wird.
        Aber das war nicht adäquat : Example 1 kann man damit nicht einmal formulieren!
     -}


    toVs' : List ( A + V + 𝒫ℱ ) → List V
    toVs' = mapMaybe ((_>>= toMaybeL) ∘ toMaybeR)
    {-
    -- again, we could have defined this explicitely

    toVs' [] = []
    toVs' (inl a ∷ avps) = toVs' avps
    toVs' (inr (inl v) ∷ avps) = v ∷ toVs' avps
    toVs' (inr (inr p) ∷ avps) = toVs' avps

    -- Instead we have used mapMaybe, toMaybeR, toMaybeL and the "bind"
    -- operator of Maybe, defined in Data.Maybe.Base as

    _>>=_ : Maybe A → (A → Maybe B) → Maybe B
    nothing >>= f = nothing
    just a  >>= f = f a

    -- Check the types! Why do we need _>>=_ ?
    -}


  infix 22 ¬_
  infix 20 _∨_
  infix 21 _∧_

  ¬_ : 𝒫ℱ → 𝒫ℱ
  ¬_ = NOT
  _∨_ _∧_ : 𝒫ℱ → 𝒫ℱ → 𝒫ℱ
  _∨_ = OR
  _∧_ f g = ¬ (¬ f ∨ ¬ g)

  infix 19 _⇒_ _⇔_
  _⇒_ _⇔_ : 𝒫ℱ → 𝒫ℱ → 𝒫ℱ
  p₁ ⇒ p₂ = (¬ p₁) ∨ p₂
  p₁ ⇔ p₂ = (p₁ ⇒ p₂) ∧ (p₂ ⇒ p₁)

  postulate
    INL : {v : V} → {M : PV} → (v ∈ M) → (N : PV) → (v ∈ (M ∪ N))
    INR : {v : V} → {N : PV} → (v ∈ N) → (M : PV) → (v ∈ (M ∪ N))
    ∈∪Lemma : {v : V} → {M N : PV} → (v ∈ (M ∪ N)) → (v ∈ M) + (v ∈ N)

  -- Hausaufgabe: Fomuliere Lemmata, die die freien Variablen von _∧_, _⇒_ und _⇔_
  -- charakterisieren.

  FVLemma∧ : (f g : 𝒫ℱ) → FreeVars ( f ∧ g ) ≡ (FreeVars f) ∪ (FreeVars g)
  FVLemma∧ f g =
    FreeVars ( f ∧ g )
      ≡⟨ refl {- Def. ∧ -} ⟩
    FreeVars (¬ (¬ f ∨ ¬ g))
      ≡⟨ refl {- FreeVars (NOT h) = FreeVars h -} ⟩
    FreeVars (¬ f ∨ ¬ g)
      ≡⟨ refl {- FreeVars (OR h h') = (FreeVars h) ∪ (FreeVars h') -}⟩
    FreeVars (¬ f) ∪ FreeVars (¬ g)
      ≡⟨ refl {- zweimal FreeVars (NOT h) = FreeVars h -} ⟩
    ((FreeVars f) ∪ (FreeVars g))
      QED

  FVLemma⇒ : (f g : 𝒫ℱ) → FreeVars ( f ⇒ g ) ≡ (FreeVars f) ∪ (FreeVars g)
  FVLemma⇒ f g = refl  {- ÜA: Expandieren in Beweis mit Equational Reasoning! -}

  FVLemma⇔ : (f g : 𝒫ℱ) → FreeVars ( f ⇔ g ) ≡ (FreeVars f) ∪ (FreeVars g)
  FVLemma⇔ f g =
    FreeVars (f ⇔ g)
      ≡⟨ refl ⟩
    FreeVars ((f ⇒ g) ∧ (g ⇒ f))
      ≡⟨ FVLemma∧ (f ⇒ g) (g ⇒ f) ⟩
    ((FreeVars (f ⇒ g)) ∪ (FreeVars (g ⇒ f)))
      ≡⟨ cong (λ x →  x ∪ (FreeVars (g ⇒ f))) (FVLemma⇒ f g) ⟩
    ((FreeVars f ∪ FreeVars g) ∪ FreeVars (g ⇒ f))
      ≡⟨ refl ⟩
    ((FreeVars f ∪ FreeVars g) ∪ (FreeVars g ∪ FreeVars f))
      ≡⟨ cong (λ x → (FreeVars f ∪ FreeVars g) ∪ x) (comm∪ _ _) ⟩
    ((FreeVars f ∪ FreeVars g) ∪ (FreeVars f ∪ FreeVars g))
      ≡⟨ idem∪ _ ⟩
    ((FreeVars f) ∪ (FreeVars g))
      QED


  -- Hausaufgabe 2 : Benutze diese, um im Beweis von example1 progress zu machen!

  example1 : V → V → V → 𝒫ℱ
  example1 x y z = FORALL ((LALA z (inr (inl x) ∷ [])) ⇔ (LALA z (inr (inl y) ∷ [])))
                           z (INL (INR (INL (∈L⇒∈ (inl refl)) _) _) _)

\end{code}
