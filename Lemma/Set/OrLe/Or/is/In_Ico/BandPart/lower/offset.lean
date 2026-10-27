import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {l i j : ℤ}
-- given
  (_ : l ≥ 2)
  (_ : 0 ≤ i)
  (h₀ : 0 ≤ j) :
-- imply
  ((j ≤ i ∧ i < l - 1) ∨ j - i ∈ Set.Ico (1 - l) 1) ∧ (j ≤ i ∨ i ≥ l - 1) ↔
    j - i ∈ Set.Ico (-l + 1) 1 := by
-- proof
  simp only [Set.mem_Ico]
  omega


-- created on 2022-01-02
-- updated on 2026-10-26
