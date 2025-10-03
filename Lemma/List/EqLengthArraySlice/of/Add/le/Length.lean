import stdlib.List
import Lemma.Algebra.Le_Sub.of.LeAdd
open Algebra


@[main]
private lemma main
  {s : List α}
  {i n : Nat}
-- given
  (h : i + n ≤ s.length) :
-- imply
  (s.array_slice i n |>.length) = n := by
-- proof
  simp [List.array_slice]
  apply Le_Sub.of.LeAdd.left.nat h


-- created on 2024-07-01
-- updated on 2025-05-13
