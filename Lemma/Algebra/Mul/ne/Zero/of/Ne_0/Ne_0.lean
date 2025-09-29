import sympy.Basic


@[main]
private lemma main
  [Mul α]
  [Zero α]
  [NoZeroDivisors α]
  {a b : α}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0) :
-- imply
  a * b ≠ 0 :=
-- proof
  mul_ne_zero h₀ h₁


-- created on 2025-03-30
-- updated on 2025-04-05
