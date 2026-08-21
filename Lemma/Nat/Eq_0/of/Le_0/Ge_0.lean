import Lemma.Nat.Eq.of.Le.Le
open Nat


@[main]
private lemma main
  [PartialOrder α]
  [Zero α]
  {x : α}
-- given
  (h_le : x ≤ 0)
  (h_ge : x ≥ 0) :
-- imply
  x = 0 :=
  Eq.of.Le.Le h_le h_ge


-- created on 2018-07-14
