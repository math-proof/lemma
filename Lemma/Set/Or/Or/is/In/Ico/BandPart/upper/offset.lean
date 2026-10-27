import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n u i j : ℤ}
-- given
  (_ : n ≥ 2)
  (_ : u ≥ 2)
  (h₀ : 0 ≤ i ∧ i < n)
  (h₁ : 0 ≤ j ∧ j < n) :
-- imply
  ((j ≥ i ∧ i ≥ n + 1 - min n u) ∨ j - i ∈ Set.Ico 0 (min n u)) ∧ (j ≥ i ∨ i < n + 1 - min n u) ↔
    j - i ∈ Set.Ico 0 u := by
-- proof
  if h : n ≤ u then
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  else
    rw [min_eq_right (le_of_not_ge h)]
    simp only [Set.mem_Ico]
    omega


-- created on 2022-01-02
-- updated on 2026-10-26
