import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
  {m : Fin n}
-- given
  (h₀ : ∀ j, x m ≤ x j) :
-- imply
  (∑ i, x i * x i) = dotProduct x x ∧ x m = sInf (Set.range x) := by
-- proof
  constructor
  ·
    simp [dotProduct]
  ·
    apply le_antisymm
    ·
      refine le_csInf (⟨x m, ⟨m, rfl⟩⟩) ?_
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      exact h₀ j
    ·
      exact csInf_le (Set.finite_range x).bddBelow ⟨m, rfl⟩


-- created on 2022-03-16
-- updated on 2026-10-17
