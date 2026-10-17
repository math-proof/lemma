import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ∀ i, x i ≤ sSup (Set.range x) := by
-- proof
  intro i
  exact le_csSup (Set.finite_range x).bddAbove ⟨i, rfl⟩


-- created on 2026-10-11
-- updated on 2026-10-17
