import sympy.Basic


@[main, comm]
private lemma main
  [DivisionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a / b / c = a / (b * c) := by
-- proof
  rw [div_mul_eq_div_div]


-- created on 2024-07-01
-- updated on 2025-10-08
