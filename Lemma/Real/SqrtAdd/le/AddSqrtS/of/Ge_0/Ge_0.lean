import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[sqrt_add_le_add_sqrt](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y) :
-- imply
  √(x + y) ≤ √x + √y :=
-- proof
  Real.sqrt_add_le_add_sqrt hx hy


-- created on 2026-10-20
