import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[triangle_or_blueStar_from_block2](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
  {i : Fin 3}
-- given
  (h0 : 6 ≤ (redBlock2 color).card)
  (hAdj : G.Adj apex (A2 i))
  (hRedApexA2 : color (s(apex, A2 i)) = 1) :
-- imply
  hasMonoTriangle G color 1 ∨ hasMonoStar G color 0 5 :=
-- proof
  PikhurkoN5.triangle_or_blueStar_from_block2 color h0 i hAdj hRedApexA2


-- created on 2026-10-22
