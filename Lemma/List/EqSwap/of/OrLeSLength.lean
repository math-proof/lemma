import Lemma.List.EqSwap.of.LeLength
open List


@[main]
private lemma main
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length ≤ i ∨ s.length ≤ j) :
-- imply
  s.swap i j = s := by
-- proof
  obtain h_i | h_j := h
  ·
    rw [EqSwap.of.LeLength.left h_i]
  ·
    rw [EqSwap.of.LeLength h_j]


-- created on 2026-07-03
