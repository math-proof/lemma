import Lemma.Vector.EqGet1_1.of.Lt
open Vector


@[main, fin]
private lemma main
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  apply EqGet1_1.of.Lt


-- created on 2025-09-23
