import sympy.Basic


@[main]
private lemma main
  {n u i j : ℤ}
-- given
  (_h_n : n ≥ 2)
  (_h_u : u ≥ 2)
  (h_i : 0 ≤ i ∧ i < n)
  (h_j : 0 ≤ j ∧ j < n) :
-- imply
  ((j ≥ i ∧ i ≥ n - min n u) ∨ j - i ∈ Set.Ico 0 (min n u)) ∧ (j ≥ i ∨ i < n - min n u) ↔
    j - i ∈ Set.Ico 0 u := by
-- proof
  rcases le_total n u with h | h
  ·
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  ·
    rw [min_eq_right h]
    simp only [Set.mem_Ico]
    omega


-- created on 2026-09-27
