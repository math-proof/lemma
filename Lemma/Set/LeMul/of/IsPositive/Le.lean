import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ}
-- given
  (hx : x ∈ Set.Ioi 0)
  (hle : g x ≤ h x) :
-- imply
  g x * x ≤ h x * x := by
-- proof
  apply mul_le_mul_of_nonneg_right hle hx.le


-- created on 2023-10-15
