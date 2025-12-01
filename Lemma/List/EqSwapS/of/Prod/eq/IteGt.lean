import Lemma.List.EqSwapS
open List


@[main]
private lemma main
  {i j i' j' : ℕ}
-- given
  (h : (⟨i', j'⟩ : ℕ × ℕ) = if i > j then
    ⟨j, i⟩
  else
    ⟨i, j⟩)
  (s : List α) :
-- imply
  s.swap i' j' = s.swap i j := by
-- proof
  split at h <;>
  ·
    injection h with h_i h_j
    simp_all [EqSwapS]


-- created on 2025-06-21
