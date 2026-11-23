import Theorem.List.Ne_Nil.is.GtLength_0
open List


/--
| attributes | lemma |
| :---: | :---: |
| path | List.Ne_Nil.is.GeLength_1 |
| comm | List.GeLength_1.is.Ne_Nil |
| mp | List.GeLength_1.of.Ne_Nil |
| mpr | List.Ne_Nil.of.GeLength_1 |
-/
@[path, comm, mp, mpr]
private lemma main
-- given
  (s : List α) :
-- imply
  s ≠ [] ↔ s.length ≥ 1 := by
-- proof
  rw [Ne_Nil.is.GtLength_0]
  aesop


-- created on 2025-10-20
-- updated on 2026-11-23
