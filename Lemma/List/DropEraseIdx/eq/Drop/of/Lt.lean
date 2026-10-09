import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.Nat.Le.of.Lt
open List Nat


@[path]
private lemma main
-- given
  (h : i < j)
  (s : List α) :
-- imply
  (s.eraseIdx i).drop j = s.drop (j + 1) := by
-- proof
  apply DropEraseIdx.eq.Drop.of.Le
  apply Le.of.Lt h


-- created on 2025-11-29
