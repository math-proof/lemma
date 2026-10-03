import sympy.Basic


@[main]
private lemma main
  [MulZeroClass α]
  [NoZeroDivisors α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  a * b ≠ 0 := by
-- proof
  exact mul_ne_zero h₀ h₁


-- created on 2026-10-03
