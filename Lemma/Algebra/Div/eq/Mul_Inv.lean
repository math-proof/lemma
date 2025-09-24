import Lemma.Basic


@[main, comm]
private lemma main
  [DivInvMonoid α]
-- given
  (a b : α) :
-- imply
  a / b = a * b⁻¹ :=
-- proof
  div_eq_mul_inv a b


-- created on 2024-07-01
-- updated on 2025-04-04
