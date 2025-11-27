import Lemma.Vector.EqGet1_1.of.Lt
open Vector


@[main]
private lemma main
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  apply EqGet1_1.of.Lt


@[main]
private lemma fin
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n).get i = 1 := by
-- proof
  apply main


-- created on 2025-09-23
