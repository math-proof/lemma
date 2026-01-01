import Lemma.Vector.EqGet0_0.of.Lt
open Vector


@[main, fin]
private lemma main
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  apply EqGet0_0.of.Lt


-- created on 2025-09-04
