Cartesisches Seminar April 2024
We read chpt.2 ("Type Theory in Principia Mathematica") of
Kamareddine, Laan, Nederpelt: "A Modern Perspective on Type Theory: From its Origins until Today"

Useful links:
- PM I https://archive.org/details/alfred-north-whitehead-bertrand-russel-principia-mathematica.-1/Alfred%20North%20Whitehead%2C%20Bertrand%20Russel%20-%20Principia%20Mathematica.%201/page/n9/mode/2up
- PM II https://archive.org/details/PrincipiaMathematicaVol2/mode/2up
- PM III https://archive.org/details/PrincipiaMathematicaVol3
- SEP on PM (by Linsky, Bernard and Irvine, Andrew David ) : https://plato.stanford.edu/entries/principia-mathematica/


\begin{code}
module Principia
\end{code}

The text starts on p 22 with the definition of the notion of a "propositional function" in
Principia Mathematica (PM):

⟫ By a "propositional function" we mean something which contains a variable x, and expresses
  a propostion as soon as a value is assigned to x. ⟪

\begin{code}
  (A : Set)          -- set(type) of individual sysmbols
  (V : Set)          -- set(type) of variables
  where
\end{code}
