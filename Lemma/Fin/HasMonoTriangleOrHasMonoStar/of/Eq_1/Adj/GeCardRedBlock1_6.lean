import Mathlib
import sympy.Basic
import sympy.analysis.Misc.erdos_613
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[triangle_or_blueStar_from_block1](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
  {i : Fin 2}
-- given
  (h0 : 6 ≤ (redBlock1 color).card)
  (hAdj : G.Adj apex (A1 i))
  (hRedApexA1 : color (s(apex, A1 i)) = 1) :
-- imply
  hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 :=
-- proof
  PikhurkoN5.triangle_or_blueStar_from_block1 color h0 i hAdj hRedApexA1


-- created on 2026-10-22
