import Lemma.Basic


@[main]
private lemma main
  [CommGroup G]
-- given
  (a b : G) :
-- imply
  a * (b / a) = b :=
-- proof
  mul_div_cancel a b


-- created on 2025-03-30
