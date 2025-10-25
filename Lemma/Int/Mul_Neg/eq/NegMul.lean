import sympy.Basic


@[main, comm]
private lemma main
  [Mul α] [HasDistribNeg α]
-- given
  (a b : α) :
-- imply
  a * -b = -(a * b) :=
-- proof
  mul_neg a b


-- created on 2024-07-01
