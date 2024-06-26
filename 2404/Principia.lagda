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
open import Data.Bool
open import Agda.Builtin.Equality
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Function.Base
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
  (a : R → ℕ)          -- arity
  -- alternative (relsyms : ℕ → Set)
  -- " R = Σ ℕ relsyms "  und " a = proj₁ "

  (_<_ : V → V → Set)  -- variables are ordered
  (PV : Set)           -- we postulate a type of sets of variables
  (_∈_ : V → PV → Set)  -- with a membership predicate
  (⟪_⟫ : List V → PV)  -- with a function from lists of variables (in particular, ∅ = ⟪[]⟫, {a} = ⟪a :: []⟫, a.s.o.
  (_∪_ : PV → PV → PV) -- featuring a union,
  (_∩_ : PV → PV → PV) -- an intersection, and
  (_-_ : PV → PV → PV) -- and a "set minus" operation.
  where

  -- as a warm-up : atomic propositions

  data AtomicProp : Set where
    MkAtomicProp : (r : R) → (args : List A) → (length args ≡ a r) → AtomicProp
    -- alternativ Lala :
    --   {n : ℕ} → relsyms n → Vect A n → AtomicProp

  ArityEq#Args : {X : Set} → R × (List X) → Set
  ArityEq#Args (r , args) = a r ≡ length args

  AtomicProp' : Set
  AtomicProp' -- = Σ R (λ r → Σ (List A) (λ args → arity r ≡ length args))
              -- = Σ (R × (List A)) (λ (r , args) → arity r ≡ length args)
              = Σ (RS × (List AS)) ArityEq#Args

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


  -- the type of propositional functions is defined mutually with the function FreeVars
  mutual
    data 𝒫 : Set where
      ATOM   : (r : R) → (args : List (A + V)) → a r ≡ length args → 𝒫
      OR     : 𝒫 → 𝒫 → 𝒫
      NOT    : 𝒫 → 𝒫
      FORALL : (f : 𝒫) → (x : V) → x ∈ (FreeVars f) → 𝒫
      Z      : List (A + V + 𝒫) → 𝒫

    FreeVars : 𝒫 → PV
    FreeVars (ATOM r avs x)     = ⟪ toVs avs ⟫
    FreeVars (OR f g)           = (FreeVars f) ∪ (FreeVars g)
    FreeVars (NOT f)            = FreeVars f
    FreeVars (FORALL f x x∈FVf) = FreeVars f - ⟪ x ∷ [] ⟫
    FreeVars (Z avps)           = ⟪ toVs' avps ⟫
       -- 1. bei uns z nicht drin, weil Konstruktor
       -- 2. Hier die einzige Stelle, wo 𝒫's vorkommen (nämlich in der Liste avps),
       --    aber FreeVars nicht rekursiv aufgerufen wird.
       -- Es ist nicht klar, ob das adäquat ist...

    toVs' : List ( A + V + 𝒫 ) → List V
    toVs' = mapMaybe ((_>>= toMaybeL) ∘ toMaybeR)
    {-
    -- again, we could have defined this explicitely

    toVs' [] = []
    toVs' (inl a ∷ avps) = toVs' avps
    toVs' (inr (inl v) ∷ avps) = v ∷ toVs' avps
    toVs' (inr (inr p) ∷ avps) = toVs' avps

    -- Instead we have used mapMaybe, toMaybeR, toMaybeL and the "bind" operator of Maybe, defined in Data.Maybe.Base as

    _>>=_ : Maybe A → (A → Maybe B) → Maybe B
    nothing >>= f = nothing
    just a  >>= f = f a

    -- Check the types! Why do we need _>>=_ ?
    -}

\end{code}
