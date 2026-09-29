import Mathlib.Data.Real.Sign
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  Real.sign (x - y) = -Real.sign (-(x - y)) := by
-- proof
  rw [Real.sign_neg, neg_neg]


-- created on 2026-09-27
