import Lemma.Vector.EqGetRange
import Lemma.Vector.Sum.eq.Sum_Get
open Vector


@[main, fin]
private lemma main
  [AddCommMonoid α]
-- given
  (v : Fin n → α) :
-- imply
  ((List.Vector.range n).map v).sum = ∑ i : Fin n, v i := by
-- proof
  rw [Sum.eq.Sum_Get]
  congr 1
  funext i
  simp [GetElem.getElem, EqGetRange.fin]


-- created on 2026-08-07
