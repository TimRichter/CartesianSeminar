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
open import Data.Nat
open import Data.List
open import Agda.Builtin.Equality
open import Data.Product
module Principia
\end{code}

The text starts on p 22 with the definition of the notion of a "propositional function" in
Principia Mathematica (PM):

⟫ By a "propositional function" we mean something which contains a variable x, and expresses
  a propostion as soon as a value is assigned to x. ⟪

\begin{code}
  (A : Set)          -- set(type) of individual sysmbols
  (V : Set)          -- set(type) of variables
  (R : Set)          -- set(type) of relation symbols
  (a : R → ℕ)
  where

  data AtomicProp : Set where
    Lala : (r : R) → (args : List A) → (length args ≡ a r) → AtomicProp

  ArityEq#Args : R × (List A) → Set
  ArityEq#Args (r , args) = a r ≡ length args

  AtomicProp' : Set
  AtomicProp' -- = Σ R (λ r → Σ (List A) (λ args → a r ≡ length args))
              -- = Σ (R × (List A)) (λ (r , args) → a r ≡ length args)
              = Σ (R × (List A)) ArityEq#Args

\end{code}
