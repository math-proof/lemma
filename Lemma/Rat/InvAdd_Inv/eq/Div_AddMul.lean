import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {b d : ℝ}
-- given
  (h₀ : b > 0)
  (h₁ : d > 0) :
-- imply
  1 / (b + 1 / d) = d / (b * d + 1) := by
-- proof
  have hd : d ≠ 0 := h₁.ne'
  have hbd : b * d + 1 ≠ 0 := by positivity
  field_simp


-- created on 2020-09-17
