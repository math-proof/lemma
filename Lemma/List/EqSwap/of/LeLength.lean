import Lemma.List.Swap
open List


@[main]
private lemma left
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length ≤ i)
  (j : ℕ) :
-- imply
  s.swap i j = s := by
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
  {s : List α}
-- given
  (h : s.length ≤ j)
  (i : ℕ) :
-- imply
  s.swap i j = s := by
-- proof
  rw [Swap]
  apply left h


-- created on 2025-06-07
