import stdlib.List
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {v : List α}
-- given
  (h : i ≤ v.length)
  (a : α) :
-- imply
  (v.insertIdx i a).length = 1 + v.length := by
-- proof
  rw [List.length_insertIdx_of_le_length h]
  rw [Add.comm]


-- created on 2025-06-08
