import sympy.Basic


@[main, comm]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
-- given
  (a b : α) :
-- imply
  -a / b = -(a / b) :=
-- proof
  neg_div b a


-- created on 2024-07-01
