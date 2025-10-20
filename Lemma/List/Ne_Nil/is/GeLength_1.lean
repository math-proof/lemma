import Lemma.List.Ne_Nil.is.GtLength_0
open List


@[main, comm, mp, mpr]
private lemma main
-- given
  (v : List α) :
-- imply
  v ≠ [] ↔ v.length ≥ 1 := by
-- proof
  rw [Ne_Nil.is.GtLength_0]
  aesop


-- created on 2025-10-20
