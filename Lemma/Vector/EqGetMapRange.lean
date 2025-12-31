import Lemma.Vector.EqGetRange
open Vector


@[main, fin]
private lemma main
-- given
  (i : Fin n) :
-- imply
  ((List.Vector.range n).map f)[i] = f i := by
-- proof
  simp [GetElem.getElem]
  congr
  simp [EqGetRange.fin]


-- created on 2025-06-29
