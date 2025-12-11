import sympy.Basic


@[main, comm]
private lemma main
  [DivisionMonoid α]
-- given
  (a b : α) :
-- imply
  a / b⁻¹ = a * b :=
-- proof
  div_inv_eq_mul a b


-- created on 2025-12-11
