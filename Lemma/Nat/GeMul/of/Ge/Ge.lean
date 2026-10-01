import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (hb : b ≥ 0)
  (hy : y ≥ 0)
  (h₀ : a ≥ b)
  (h₁ : x ≥ y) :
-- imply
  a * x ≥ b * y := by
-- proof
  exact mul_le_mul h₀ h₁ hy (le_trans hb h₀)


-- created on 2019-01-10
