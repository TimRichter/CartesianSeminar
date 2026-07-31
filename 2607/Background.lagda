\begin{code}
module Background where

open import Relation.Binary.PropositionalEquality as PE
open PE.≡-Reasoning
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Relation.Nullary using (¬_)

infix  15 _≤_
infixr 20 _+_
infixr 21 _*_
infixl 20 _-_
infixl 21 _/_

postulate
  ℝ : Set
  _+_ : ℝ → ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ
  _-_ : ℝ → ℝ → ℝ
  0ℝ  : ℝ
  1ℝ  : ℝ
  _/_ : ℝ → Σ ℝ (λ r → r ≢ 0ℝ) → ℝ

  -- Benötigte algebraische Gesetze (Körpereigenschaften)
  +-comm  : ∀ (x y : ℝ)   → x + y ≡ y + x
  +-assoc : ∀ (x y z : ℝ) → (x + y) + z ≡ x + (y + z)
  *-comm  : ∀ (x y : ℝ)   → x * y ≡ y * x
  *-assoc : ∀ (x y z : ℝ) → (x * y) * z ≡ x * (y * z)
  distrib : ∀ (x y z : ℝ) → x * (y + z) ≡ (x * y) + (x * z)

  -- Identitäten
  *-identity^l : ∀ (x : ℝ) → 1ℝ * x ≡ x
  +-identity^l : ∀ (x : ℝ) → 0ℝ + x ≡ x

  -- Die entscheidende Brücken-Regel für die Bruchrechnung bei Bayes:
  -- Sie erlaubt es, von "P(A|B) * P(B) = P(A ∩ B)" zu "P(A|B) = P(A ∩ B) / P(B)" zu kommen.
  division-lemma : ∀ (x y z : ℝ) (nz : z ≢ 0ℝ) → x * z ≡ y → x ≡ y / (z , nz)

  -- ≤ on ℝ
  _≤_ : ℝ → ℝ → Set

infix 20 [_∥_]
[_∥_] : ℝ → ℝ → (ℝ → Set)
[ x ∥ y ] z = x ≤ z × z ≤ y


postulate
  Ω : Set

{- vielleicht statt PΩ allgemeiner:
Pow : Set → Set₁
Pow A = A → Set
    ... ?
-}

PΩ : Set₁
PΩ = Ω → Set   -- (oder eventuell Ω → 𝔹 ?)

{- Beispiel Würfel
 Ω = {1,2,3,4,5,6}
 Teilmenge {2,4,6} entspricht der Funktion
 evenCube : {1,2,3,4,5,6} → Set
 evenCube 1 = ⊥ (leerer Typ)
 evenCube 2 = ⊤ (singleton Typ)
 ...
-}

∅Ω : PΩ ; ∅Ω ω = ⊥

ΩΩ : PΩ ; ΩΩ ω = ⊤

infix 15 _∈_
_∈_ : Ω → PΩ → Set ; ω ∈ A = A ω

infix 15 _⊆_
_⊆_ : PΩ → PΩ → Set ; A ⊆ B = ∀ ω → ω ∈ A → ω ∈ B

infix 15 _==_
_==_ : PΩ → PΩ → Set ; A == B = A ⊆ B × B ⊆ A

⊆refl : ∀ A → A ⊆ A ; ⊆refl A ω ω∈A = ω∈A

⊆trans : ∀ {A B C} → A ⊆ B → B ⊆ C → A ⊆ C
⊆trans A⊆B B⊆C ω ω∈A = B⊆C ω (A⊆B ω ω∈A)

==refl : ∀ A → A == A ; ==refl A = (⊆refl A , ⊆refl A)

==trans : ∀ {A B C} → A == B → B == C → A == C
==trans (A⊆B , B⊆A) (B⊆C , C⊆B) = (⊆trans A⊆B B⊆C , ⊆trans C⊆B B⊆A)

==symm : ∀ {A B} → A == B → B == A
==symm (A⊆B , B⊆A) = (B⊆A , A⊆B)

-- ==-reasoning

infix 3 _==∎
_==∎ : ∀ A → A == A
A ==∎ = ==refl A

step-== : ∀ A {B C} → A == B → B == C → A == C
step-== A A==B B==C = ==trans A==B B==C
infixr 2 step-==
syntax step-== A A==B B==C = A ==⟨ A==B ⟩ B==C

step-==˘ : ∀ A {B C} → B == A → B == C → A == C
step-==˘ A B==A B==C = ==trans (==symm B==A) B==C
infixr 2 step-==˘
syntax step-==˘ A B==A B==C = A ==˘⟨ B==A ⟩ B==C

all⊆ΩΩ : ∀ A → A ⊆ ΩΩ ; all⊆ΩΩ A = λ ω x → tt

all∅Ω⊆ : ∀ A → ∅Ω ⊆ A ; all∅Ω⊆ A ω ()

infixr 17 _∩_
infixr 16 _∪_
infixl 18 _\\_
_∩_ _∪_ _\\_ : PΩ → PΩ → PΩ
(A ∩ B)  ω = ω ∈ A × ω ∈ B
(A ∪ B)  ω = ω ∈ A ⊎ ω ∈ B
(A \\ B) ω = ω ∈ A × ¬ (ω ∈ B)

congLeft∩ : ∀ A → ∀ {B C} → B == C → A ∩ B == A ∩ C
congLeft∩ A (B⊆C , C⊆B) = ((λ ω (ω∈A , ω∈B) → (ω∈A , B⊆C ω ω∈B)) ,
                           (λ ω (ω∈A , ω∈C) → (ω∈A , C⊆B ω ω∈C)))

congRight∩ : ∀ A → ∀ {B C} → B == C → B ∩ A == C ∩ A
congRight∩ A (B⊆C , C⊆B) = ((λ ω (ω∈B , ω∈A) → (B⊆C ω ω∈B , ω∈A)) ,
                            (λ ω (ω∈C , ω∈A) → (C⊆B ω ω∈C , ω∈A)))

-- universal property of ∩, split into 3 parts

∩-UP1 : ∀ {A B} → A ∩ B ⊆ A
∩-UP1 ω (ω∈A , ω∈B) = ω∈A

∩-UP2 : ∀ {A B} → A ∩ B ⊆ B
∩-UP2 ω (ω∈A , ω∈B) = ω∈B

∩-UP3 : ∀ {A B C} → C ⊆ A → C ⊆ B → C ⊆ A ∩ B
∩-UP3 C⊆A C⊆B ω ω∈C = (C⊆A ω ω∈C) , (C⊆B ω ω∈C)

∩⊆-Lemma : ∀ {A B} → A ⊆ B → A ∩ B == A
∩⊆-Lemma {A} A⊆B = (∩-UP1 , ∩-UP3 (⊆refl A) A⊆B)

-- univeral property of ∪, split into 3 parts

∪-UP1 : ∀ {A B} → A ⊆ A ∪ B
∪-UP1 ω ω∈A = inj₁ ω∈A

∪-UP2 : ∀ {A B} → B ⊆ A ∪ B
∪-UP2 ω ω∈B = inj₂ ω∈B

∪-UP3 : ∀ {A B C} → A ⊆ C → B ⊆ C → A ∪ B ⊆ C
∪-UP3 A⊆C B⊆C ω (inj₁ ω∈A) = A⊆C ω ω∈A
∪-UP3 A⊆C B⊆C ω (inj₂ ω∈B) = B⊆C ω ω∈B

∪⊆-Lemma : ∀ {A B} → A ⊆ B → A ∪ B == B
∪⊆-Lemma {B = B} A⊆B = (∪-UP3 A⊆B (⊆refl B) , ∪-UP2)

∩-assoc : ∀ {A B C} → (A ∩ B) ∩ C == A ∩ B ∩ C
∩-assoc = (∩-UP3 (λ ω (( ω∈A , _) , _) → ω∈A) (λ ω ((_ , ω∈B), ω∈C) → (ω∈B , ω∈C)) ,
           ∩-UP3 (λ ω (ω∈A , (ω∈B , _)) → (ω∈A , ω∈B)) (λ ω (_ , (_ , ω∈C)) → ω∈C))

∩-idem : ∀ {A} → A ∩ A == A
∩-idem {A} = (∩-UP1 , ∩-UP3 (⊆refl A) (⊆refl A))

-- extensional equality and funext

infix 20 _≐_
_≐_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ≐ g = ∀ a → f a ≡ g a

postulate
  funext : ∀ {A B} → (f g : A → B) → f ≐ g → f ≡ g
\end{code}

Ziel: Bayes' Theorem (klassische Variante) formulieren und aus den
(postulierten und bewiesenen) Eigenschaften beweisen.

\begin{code}

disjoint : PΩ → PΩ → Set
disjoint A B = (A ∩ B) == ∅Ω
\end{code}

Nathan hatte

disjPair : PΩ → PΩ → Set
disjPair A B = ∀ e → ¬ ((e ∈ A) × (e ∈ B))

Das ist aber equivalent, und disjoint ist "semantischer"...

disj-Lemma1 : ∀ {A B} → disjoint A B → disjPair A B
disj-Lemma1 A∩B=∅ e e∈A∩B = proj₁ A∩B=∅ e e∈A∩B

disj-Lemma2 : ∀ {A B} → disjPair A B → disjoint A B
disj-Lemma2 {A} {B} dP = (A∩B⊆∅ , ∅⊆A∩B) where
  A∩B⊆∅ : A ∩ B ⊆ ∅Ω
  A∩B⊆∅ ω ω∈A∩B = dP ω ω∈A∩B
  ∅⊆A∩B : ∅Ω ⊆ A ∩ B
  ∅⊆A∩B ω ()

\begin{code}
∩-comm : ∀ A B → A ∩ B == B ∩ A
∩-comm A B = ((λ ω (ω∈A , ω∈B) → (ω∈B , ω∈A)) ,
              (λ ω (ω∈B , ω∈A) → (ω∈A , ω∈B)))

∩∪-dist : ∀ A B C → A ∩ (B ∪ C) == (A ∩ B) ∪ (A ∩ C)
∩∪-dist A B C = (l⊆r , r⊆l) where
  l⊆r : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C)
  l⊆r ω (ω∈A , inj₁ ω∈B) = inj₁ (ω∈A , ω∈B)
  l⊆r ω (ω∈A , inj₂ ω∈C) = inj₂ (ω∈A , ω∈C)
  r⊆l : (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C)
  r⊆l ω (inj₁ (ω∈A , ω∈B)) = (ω∈A , inj₁ ω∈B)
  r⊆l ω (inj₂ (ω∈A , ω∈C)) = (ω∈A , inj₂ ω∈C)

compl : PΩ → PΩ
compl A = ΩΩ \\ A

postulate
  ∪compl : ∀ A → A ∪ compl A == ΩΩ
  -- cannot be proven ... A : Ω → Set would have to be a decidable predicate.

∩compl : ∀ A → A ∩ compl A == ∅Ω
∩compl A = ((λ ω (ω∈A , (_ , ω∉A)) → ω∉A ω∈A ) , all∅Ω⊆ _)

postulate
  -- Wahrscheinlichkeit
  P : PΩ → ℝ

-- Diese Bedingungen gehören zur Kolmogoroff'schen Theorie, werden
-- aber für BT nicht benötigt.
  -- Begrenztheit : 0 ≤ P x ≤ 1
  --Pbound : ∀ (A : PΩ) → [ 0ℝ ∥ 1ℝ ] (P A)
  Pbound : ∀ (A : PΩ) → 0ℝ ≤ (P A) × (P A) ≤ 1ℝ

  -- Normiertheit : P Q = 1R
  Pnorm : P ΩΩ ≡ 1ℝ

  -- paarweise Additivität
  Padditiv : ∀ (A B : PΩ) → disjoint A B → P (A ∪ B) ≡ P A + P B
  -- endliche Additivität folgt durch Iteration
  -- Sigma-Additivität nicht, aber die brauchen wir auch nicht.

postulate

  -- mit Eigenschaften von WMaß lassen sich einige Postulate eventuell auch beweisen
  -- (Tim: hmm, diese wohl nicht...)

  Pcond : PΩ → PΩ → ℝ

  Pcong : ∀ (A B : PΩ) → A == B → P A ≡ P B

  condProd : ∀ (A B : PΩ) → (Pcond A B) * P B ≡ P (A ∩ B)


BT : ∀ (A B : PΩ) → (n0B : P B ≢ 0ℝ) → Pcond A B ≡ (Pcond B A * P A) / (P B , n0B)
BT A B n0B =
  let
    eq : Pcond A B ≡ P (A ∩ B) / (P B , n0B)
    eq = division-lemma (Pcond A B) (P (A ∩ B)) (P B) n0B (condProd A B)
  in
    Pcond A B                        ≡⟨ eq ⟩
    P (A ∩ B) / (P B , n0B)          ≡⟨ cong (_/ (P B , n0B)) (Pcong (A ∩ B) (B ∩ A) (∩-comm A B)) ⟩
    P (B ∩ A) / (P B , n0B)          ≡⟨ cong (_/ (P B , n0B)) (sym (condProd B A)) ⟩
    (Pcond B A * P A) / (P B , n0B)  ∎


\end{code}

In der Formel im Buch kommen nur bedingte Wkn. vor, in den Bedingungen steht immer
"background knowledge" , oft nichts anderes.

P(h | e ∩ b) = P (h | b) * P (e | h ∩ b) / (P( h | b) * P (e | h ∩ b) + P (¬ h | b) * P (e | ¬ h ∩ b))

Wir zeigen zuerst

P(h | e) = P (h) * P (e | h) / ( P (h) * P (e | h) + P (¬ h) * P (e | ¬ h) )

(d.h. wir ersetzen P ( h | b)  durch P (h)).

\begin{code}

Prelim : ∀ H E →  ((P H) * (Pcond E H)) + (P (ΩΩ \\ H)) * (Pcond E (ΩΩ \\ H)) ≡ P E
Prelim H E =
  let
    eq1 : P H * Pcond E H ≡ P (E ∩ H)
    eq1 = P H * Pcond E H  ≡⟨ *-comm _ _ ⟩
          Pcond E H * P H  ≡⟨ condProd _ _ ⟩
          P (E ∩ H)            ∎
    eq2 : P (ΩΩ \\ H) * Pcond E (ΩΩ \\ H) ≡ P (E ∩ (ΩΩ \\ H))
    eq2 = P (ΩΩ \\ H) * Pcond E (ΩΩ \\ H)  ≡⟨ *-comm _ _ ⟩
          Pcond E (ΩΩ \\ H) * P (ΩΩ \\ H)  ≡⟨ condProd _ _ ⟩
          P (E ∩ (ΩΩ \\ H))            ∎
    dj : disjoint (E ∩ H) (E ∩ (ΩΩ \\ H))
    dj = (E ∩ H) ∩ (E ∩ (compl H))  ==⟨ ∩-assoc ⟩
          E ∩ H ∩ E ∩ (compl H)     ==˘⟨ congLeft∩ E ∩-assoc ⟩
          E ∩ (H ∩ E) ∩ (compl H)   ==⟨ congLeft∩ E (congRight∩ (compl H) (∩-comm H E)) ⟩
          E ∩ (E ∩ H) ∩ (compl H)   ==⟨ congLeft∩ E ∩-assoc ⟩
          E ∩ E ∩ H ∩ (compl H)     ==˘⟨ ∩-assoc ⟩
          (E ∩ E) ∩ H ∩ (compl H)   ==⟨ congLeft∩ (E ∩ E) (∩compl H) ⟩
          (E ∩ E) ∩ ∅Ω              ==⟨ (∩-UP2 , all∅Ω⊆ _) ⟩
          ∅Ω                        ==∎
  in
      ((P H) * (Pcond E H)) + (P (ΩΩ \\ H)) * (Pcond E (ΩΩ \\ H))
        ≡⟨ cong (_+ (P (ΩΩ \\ H)) * (Pcond E (ΩΩ \\ H))) eq1 ⟩
      P (E ∩ H) + (P (ΩΩ \\ H)) * (Pcond E (ΩΩ \\ H))
        ≡⟨ cong ( P (E ∩ H) +_) eq2 ⟩
      P (E ∩ H) + P (E ∩ (ΩΩ \\ H))
        ≡⟨ sym (Padditiv _ _ dj) ⟩
      P ((E ∩ H) ∪ (E ∩ (ΩΩ \\ H)))
        ≡⟨ sym (Pcong _ _ (∩∪-dist E H (ΩΩ \\ H))) ⟩
      P (E ∩ (H ∪ (ΩΩ \\ H)))
        ≡⟨ Pcong _ _ (congLeft∩ E (∪compl H)) ⟩
      P (E ∩ ΩΩ)
        ≡⟨ Pcong _ _ (∩⊆-Lemma (all⊆ΩΩ E)) ⟩
      P E  ∎


{- t.b.c.

Formel : ∀ {H E} → (n0E : P E ≢ 0ℝ) →
         Pcond H E ≡ ((P H) * (Pcond E H)) /
                  ( ((P H) * (Pcond E H)) + (P (ΩΩ \\ H)) * (Pcond E (ΩΩ \\ H)) , {!!} )
Formel = {!!}

-}

\end{code}
