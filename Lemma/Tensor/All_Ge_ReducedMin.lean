import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ∀ i, sInf (Set.range x) ≤ x i := by
-- proof
  intro i
  exact csInf_le (Set.finite_range x).bddBelow ⟨i, rfl⟩


-- created on 2023-10-04
-- updated on 2026-10-26
