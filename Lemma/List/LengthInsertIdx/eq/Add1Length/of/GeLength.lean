import stdlib.List
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a).length = 1 + s.length := by
-- proof
  rw [List.length_insertIdx_of_le_length h]
  rw [Add.comm]


-- created on 2025-06-08
