import sympy.Basic


@[main, comm]
private lemma main
  [DivisionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a * b / c = a / c * b :=
-- proof
  mul_div_right_comm a b c


-- created on 2024-07-01
