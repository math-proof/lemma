import Lemma.Vector.EqGet0_0.of.Lt
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  apply EqGet0_0.of.Lt


@[main]
private lemma fin
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n).get i = 0 := by
-- proof
  apply main


-- created on 2025-09-04
