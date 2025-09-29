import sympy.Basic


@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
  (a b : α) :
-- imply
  -(a * b) = -a * b :=
-- proof
  neg_mul_eq_neg_mul a b


-- created on 2024-07-01
