import sympy.Basic


@[main]
private lemma main
  [DivisionCommMonoid α]
  -- given
  (a b x y : α) :
-- imply
  (a / b) * (x / y) = a * x / (b * y) :=
-- proof
  div_mul_div_comm a b x y


-- created on 2025-12-09
