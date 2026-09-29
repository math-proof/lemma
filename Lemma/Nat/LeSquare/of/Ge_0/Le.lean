import sympy.Basic


@[main]
private lemma main
  {x M : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x ≤ M) :
-- imply
  x * x ≤ M * M :=
-- proof
  mul_self_le_mul_self h₀ h₁


-- created on 2026-09-27
