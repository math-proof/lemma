import Lemma.Vector.Sub.eq.Sub_Replicate
open Vector


@[main, fin]
private lemma main
  [SubNegMonoid α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x - a)[i] = x[i] - a := by
-- proof
  simp [GetElem.getElem]
  rw [Sub.eq.Sub_Replicate]
  rw [GetSub.eq.SubGetS.fin]
  simp


-- created on 2025-12-03
