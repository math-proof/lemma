import Batteries.Data.List.Lemmas
import Lemma.List.DropSet.eq.Drop.of.Lt
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
  (s.swap i j).drop (j + 1) = s.drop (j + 1) := by
-- proof
  if h_j : j < s.length then
    have h_i := Lt.of.Lt.Lt h h_j
    rw [List.swap_eq_of_lt h_i h_j]
    rw [DropSet.eq.Drop.of.Lt (by linarith)]
    rw [DropSet.eq.Drop.of.Lt (by linarith)]
  else
    grind [List.swap_eq_of_ge_right]


-- created on 2025-05-17
-- updated on 2026-08-24
