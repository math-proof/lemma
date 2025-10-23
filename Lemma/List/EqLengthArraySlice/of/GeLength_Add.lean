import stdlib.List
import Lemma.Nat.Le_Sub.of.LeAdd
open Nat


@[main]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length ≥ i + d) :
-- imply
  (s.array_slice i d |>.length) = d := by
-- proof
  simp [List.array_slice]
  apply Le_Sub.of.LeAdd.left h


-- created on 2024-07-01
-- updated on 2025-05-13
