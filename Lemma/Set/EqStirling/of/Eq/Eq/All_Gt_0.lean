import sympy.Basic


@[path]
private lemma main
  {k : ℕ}
  {x : Fin k → Set α}
  {j : Fin k}
-- given
  (h₀ : ∀ i, i ≠ j → Disjoint (x i) (x j)) :
-- imply
  (⋃ i ∈ ({i | i ≠ j} : Set (Fin k)), x i) \ x j = ⋃ i ∈ ({i | i ≠ j} : Set (Fin k)), x i := by
-- proof
  ext a
  simp only [Set.mem_sdiff, Set.mem_iUnion]
  refine ⟨fun h => h.1, ?_⟩
  intro h
  refine ⟨h, ?_⟩
  intro ha
  obtain ⟨i, hi, hai⟩ := h
  exact (h₀ i hi).le_bot ⟨hai, ha⟩


-- created on 2026-10-11
-- updated on 2026-10-17
