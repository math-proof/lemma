import Lemma.Nat.Ne.of.Gt
import Theorem.List.Ne_Nil.of.NeLength_0
open List Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | List.Ne_Nil.is.GtLength_0 |
| comm | List.GtLength_0.is.Ne_Nil |
| mp | List.GtLength_0.of.Ne_Nil |
| mpr | List.Ne_Nil.of.GtLength_0 |
-/
@[path, comm, mp, mpr]
private lemma main
-- given
  (s : List α) :
-- imply
  s ≠ [] ↔ s.length > 0 := by
-- proof
  constructor <;>
    intro h
  ·
    by_contra h
    simp at h
    contradiction
  ·
    apply Ne_Nil.of.NeLength_0 (Ne.of.Gt h)


-- created on 2025-05-08
-- updated on 2026-11-23
