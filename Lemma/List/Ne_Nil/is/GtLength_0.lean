import Lemma.Nat.Ne.of.Gt
import Lemma.List.Ne_Nil.of.NeLength_0
open List Nat


@[main, comm, mp, mpr]
private lemma main
-- given
  (s : List α) :
-- imply
  s ≠ [] ↔ s.length > 0 := by
-- proof
  constructor <;>
    intro h
  .
    by_contra h
    simp at h
    contradiction
  ·
    have h := Ne.of.Gt h
    apply Ne_Nil.of.NeLength_0 h


-- created on 2025-05-08
