import stdlib.List
import Lemma.List.EqSwapS
open List


@[main]
private lemma left
  {a : List α}
  {i : ℕ}
-- given
  (h : i ≥ a.length)
  (j : ℕ) :
-- imply
  a.swap i j = a := by
-- proof
  unfold List.swap
  split_ifs with h_eq h_lt? h_j h_i
  ·
    rfl
  ·
    linarith
  ·
    rfl
  ·
    linarith
  ·
    rfl


@[main]
private lemma main
  {a : List α}
-- given
  (h : j ≥ a.length)
  (i : ℕ) :
-- imply
  a.swap i j = a := by
-- proof
  rw [EqSwapS]
  apply left h


-- created on 2025-06-07
