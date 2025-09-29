import Lemma.Basic


@[main, comm]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
-- given
  (a b : α) :
-- imply
  a / -b = -(a / b) :=
-- proof
  div_neg a


-- created on 2024-07-01
