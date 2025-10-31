import stdlib.List
import Lemma.Nat.EqSubAdd
open Nat


@[main]
private lemma main
-- given
  (s : List α) :
-- imply
  (s.drop i).take d = s.slice i (i + d) := by
-- proof
  unfold List.slice List.array_slice Function.comp
  rw [EqSubAdd.left]


-- created on 2025-06-18
