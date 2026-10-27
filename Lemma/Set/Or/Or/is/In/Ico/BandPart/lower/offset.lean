import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n l i j : ℤ}
-- given
  (_ : n ≥ 2)
  (_ : l ≥ 2)
  (h₀ : 0 ≤ i ∧ i < n)
  (h₁ : 0 ≤ j ∧ j < n) :
-- imply
  ((j < i ∧ i < min n l - 1) ∨ j - i ∈ Set.Ico (1 - min n l) 0) ∧ (j < i ∨ i ≥ min n l - 1) ↔
    j - i ∈ Set.Ico (-l + 1) 0 := by
-- proof
  if h : n ≤ l then
    rw [min_eq_left h]
    simp only [Set.mem_Ico]
    omega
  else
    rw [min_eq_right (le_of_not_ge h)]
    simp only [Set.mem_Ico]
    omega


-- created on 2022-01-02
-- updated on 2026-10-26
