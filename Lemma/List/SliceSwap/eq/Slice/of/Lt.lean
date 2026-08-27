import Batteries.Data.List.Lemmas
import Lemma.List.Slice.eq.DropTake
import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.List.TakeSet.eq.Take.of.Ge
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.NotLt.is.Ge
open List Nat


@[main]
private lemma main
  {i j : ℕ}
-- given
  (h : i < j)
  (s : List α) :
-- imply
  (s.swap i j).slice (i + 1) j = s.slice (i + 1) j := by
-- proof
  if h_j : j < s.length then
    have h_i := Lt.of.Lt.Lt h h_j
    rw [List.swap_eq_of_lt h_i h_j]
    rw [Slice.eq.DropTake]
    rw [TakeSet.eq.Take.of.Ge (by rfl)]
    rw [TakeSet.eq.SetTake.of.Lt h]
    rw [DropSet.eq.Drop.of.Lt (by linarith)]
    rw [← Slice.eq.DropTake]
  else
    grind [List.swap_eq_of_ge_right]


-- created on 2025-05-17
-- updated on 2026-08-24
