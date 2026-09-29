import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a m M : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : m ≥ 0)
  (h₂ : m < M) :
-- imply
  max (m ^ 2 * a) (M ^ 2 * a) = m ^ 2 * a := by
-- proof
  have h : m ^ 2 ≤ M ^ 2 := by nlinarith
  exact max_eq_left (by nlinarith)


-- created on 2026-09-27
