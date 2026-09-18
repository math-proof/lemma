import sympy.Basic


@[main, comm]
private lemma main
  [DivisionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a / b * c = a * (c / b) :=
-- proof
  mul_comm_div a b c


-- created on 2026-09-18
