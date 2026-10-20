import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ} :
-- imply
  ∀ i, x i ≤ sSup (Set.range x) ∧ -x i ≤ sSup (Set.range fun j => -x j) := by
-- proof
  intro i
  constructor
  ·
    exact le_csSup (Set.finite_range x).bddAbove ⟨i, rfl⟩
  ·
    exact le_csSup (Set.finite_range (fun j => -x j)).bddAbove ⟨i, rfl⟩


-- created on 2023-11-12
-- updated on 2026-10-17
