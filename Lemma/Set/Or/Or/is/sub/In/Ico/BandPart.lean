import sympy.Basic


@[main]
private lemma lower
  {l i j : ℤ}
-- given
  (_h_l : l ≥ 2)
  (_h_i : 0 ≤ i)
  (h_j : 0 ≤ j) :
-- imply
  ((j ≤ i ∧ i < l) ∨ j - i ∈ Set.Ico (1 - l) 1) ∧ (j ≤ i ∨ i ≥ l) ↔ j - i ∈ Set.Ico (-l + 1) 1 := by
-- proof
  simp only [Set.mem_Ico]
  omega


-- created on 2026-09-27
