import stdlib.List
import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n ≥ s.length) :
-- imply
  (s.array_slice i n).length = s.length - i := by
-- proof
  simp [List.array_slice]
  rwa [Add.comm]


-- created on 2025-05-13
