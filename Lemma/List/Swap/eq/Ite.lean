import stdlib.List
import Batteries.Data.List.Lemmas
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.List.DropSet.eq.Drop.of.Lt
import Lemma.List.TakeSet.eq.SetTake.of.Lt
import Lemma.List.TakeTake.eq.Take.of.Ge
import Lemma.List.Slice.eq.DropTake
import Lemma.List.LengthSet.eq.Length
import Lemma.Nat.Lt.of.Lt.Lt
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.NotLt.is.Ge
import Lemma.Nat.Lt.is.Le.Ne
open List Nat


private lemma of_Lt
  {s : List α}
  {i j : ℕ}
-- given
  (h_ij : i < j)
  (h_j : j < s.length) :
-- imply
  s.swap i j = s.take i ++ s[j] :: s.slice (i + 1) j ++ s[i] :: s.drop (j + 1) := by
-- proof
  have h_i : i < s.length := Lt.of.Lt.Lt h_ij h_j
  rw [List.swap_eq_of_lt h_i h_j]
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by simpa [LengthSet.eq.Length])]
  rw [DropSet.eq.Drop.of.Lt (by linarith)]
  rw [TakeSet.eq.SetTake.of.Lt h_ij]
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by simp; omega)]
  rw [TakeTake.eq.Take.of.Ge (Le.of.Lt h_ij)]
  rw [← Slice.eq.DropTake]


@[main]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  s.swap i j =
    if i = j then
      s
    else if h_lt : i < j then
      if h_j : j < s.length then
        s.take i ++ s[j] :: s.slice (i + 1) j ++ s[i] :: s.drop (j + 1)
      else
        s
    else if h_i : i < s.length then
      s.take j ++ s[i] :: s.slice (j + 1) i ++ s[j] :: s.drop (i + 1)
    else
      s := by
-- proof
  split_ifs with h_eq h_lt h_j h_i
  ·
    rw [h_eq]
    apply List.swap_self
  ·
    apply of_Lt h_lt h_j
  ·
    apply List.swap_eq_of_ge_right
    apply Ge.of.NotLt h_j
  ·
    rw [List.swap_comm]
    apply of_Lt _ h_i
    apply Lt.of.Le.Ne
    ·
      apply Ge.of.NotLt h_lt
    ·
      intro h
      apply h_eq
      exact h.symm
  ·
    apply List.swap_eq_of_ge_left
    apply Ge.of.NotLt h_i


-- created on 2025-05-17
-- updated on 2026-08-24
