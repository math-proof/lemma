import Lemma.Vector.EqGet_1.of.Eq_1.Lt
open Vector


@[main]
private lemma main
  [One α]
-- given
  (h_i : i < n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  apply EqGet_1.of.Eq_1.Lt
  rfl


-- created on 2025-09-23
