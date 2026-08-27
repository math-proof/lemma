import Batteries.Data.List.Lemmas
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
  (s.swap i j).take i = s.take i := by
-- proof
  if h_j : j < s.length then
    have h_i := Lt.of.Lt.Lt h h_j
    rw [List.swap_eq_of_lt h_i h_j]
    rw [TakeSet.eq.Take.of.Ge (by linarith)]
    rw [TakeSet.eq.Take.of.Ge (by rfl)]
  else
    grind [List.swap_eq_of_ge_right]


-- created on 2025-05-17
-- updated on 2026-08-24
