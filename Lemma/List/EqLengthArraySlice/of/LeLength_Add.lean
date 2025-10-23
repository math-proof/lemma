import stdlib.List
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length ≤ i + d) :
-- imply
  (s.array_slice i d).length = s.length - i := by
-- proof
  simp [List.array_slice]
  rwa [Add.comm]


-- created on 2025-05-13
