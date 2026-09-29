import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y z : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : 1 + y * x = z * x) :
-- imply
  1 / x + y = z := by
-- proof
  have hx := h₀.ne'
  field_simp
  linarith


-- created on 2026-09-27
