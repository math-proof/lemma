import sympy.core.numbers
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  ↑x + I * ↑y = 0 ↔ x = 0 ∧ y = 0 := by
-- proof
  rw [Complex.ext_iff]
  simp


-- created on 2025-01-05
