import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a m M : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : M ≤ 0)
  (h₂ : m < M) :
-- imply
  max (m ^ 2 * a) (M ^ 2 * a) = M ^ 2 * a := by
-- proof
  have h : M ^ 2 ≤ m ^ 2 := by nlinarith
  exact max_eq_right (by nlinarith)


-- created on 2021-10-02
