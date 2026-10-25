import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators
open PikhurkoN5.V
open PikhurkoN5


/--
[exists_block_receives_at_least_6_red](https://github.com/teorth/analysis/blob/main/Analysis/Misc/erdos_613.lean)
-/
@[path]
private lemma main
  {color : Sym2 V → Fin 2}
-- given
  (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
-- imply
  (redBlock1 color).card ≥ 6 ∨ (redBlock2 color).card ≥ 6 :=
-- proof
  PikhurkoN5.exists_block_receives_at_least_6_red color hNoBlueStar


-- created on 2026-10-22
