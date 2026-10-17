import Lemma.Real.LeLog.of.Le
import sympy.Basic
open Real


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : x ≤ y) :
-- imply
  Real.log x ≤ Real.log y := by
-- proof
  apply LeLog.of.Le h₀ h₁


-- created on 2026-10-17
