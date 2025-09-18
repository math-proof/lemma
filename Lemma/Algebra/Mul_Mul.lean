import Lemma.Basic


@[main]
private lemma Comm
  [CommSemigroup G]
-- given
  (a b c : G) :
-- imply
  a * (b * c) = b * (a * c) :=
-- proof
  mul_left_comm a b c


-- created on 2025-06-06
