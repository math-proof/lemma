import sympy.Basic


@[path]
private lemma main
  {n l i j : ℤ}
-- given
  (_h_n : n ≥ 2)
  (_h_l : l ≥ 2)
  (h_i : 0 ≤ i ∧ i < n)
  (h_j : 0 ≤ j ∧ j < n) :
-- imply
  ((j ≤ i ∧ i < min n l - 1) ∨ j - i ∈ Set.Ico (1 - min n l) 1) ∧ (j ≤ i ∨ i ≥ min n l - 1) ↔
    j - i ∈ Set.Ico (-l + 1) 1 := by
-- proof
  rcases le_total n l with h | h
  ·
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  ·
    rw [min_eq_right h]
    simp only [Set.mem_Ico]
    omega


-- created on 2022-03-29
-- updated on 2023-05-21
