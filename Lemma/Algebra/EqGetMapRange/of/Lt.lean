import Lemma.Algebra.EqGetMapRange
open Algebra


@[main]
private lemma main
-- given
  (h : i < n)
  (f : Fin n → α) :
-- imply
  ((List.Vector.range n).map f)[i] = f ⟨i, h⟩ := by
-- proof
  rw [GetElem.getElem]
  apply EqGetMapRange.fin


-- created on 2025-06-29
