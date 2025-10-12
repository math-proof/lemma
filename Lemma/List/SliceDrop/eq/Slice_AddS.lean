import stdlib.List
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.EqSubAdd
open Nat


@[main]
private lemma main
-- given
  (s : List α)
  (n i j : ℕ) :
-- imply
  (s.drop n).slice i j = s.slice (n + i) (n + j) := by
-- proof
  unfold List.slice List.array_slice Function.comp
  simp
  repeat rw [Sub_Add.eq.SubSub]
  rw [EqSubAdd.left]


-- created on 2025-06-17
