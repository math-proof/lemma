import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ}
  {m : Fin n}
-- given
  (h₀ : ∀ j, x j = y j)
  (h₁ : ∀ j, x m ≤ x j) :
-- imply
  y m = sInf (Set.range y) := by
-- proof
  have hmin : ∀ j, y m ≤ y j := by
    intro j
    simpa [h₀ m, h₀ j] using h₁ j
  apply le_antisymm
  ·
    refine le_csInf (⟨y m, ⟨m, rfl⟩⟩) ?_
    intro z hz
    obtain ⟨j, rfl⟩ := hz
    exact hmin j
  ·
    exact csInf_le (Set.finite_range y).bddBelow ⟨m, rfl⟩


-- created on 2020-12-19
-- updated on 2026-10-17
