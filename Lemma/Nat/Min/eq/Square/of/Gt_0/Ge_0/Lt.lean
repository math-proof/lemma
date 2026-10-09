import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a m M : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : m ≥ 0)
  (h₂ : m < M) :
-- imply
  min (m ^ 2 * a) (M ^ 2 * a) = m ^ 2 * a := by
-- proof
  have h : m ^ 2 ≤ M ^ 2 := by nlinarith
  exact min_eq_left (mul_le_mul_of_nonneg_right h h₀.le)


-- created on 2021-10-02
