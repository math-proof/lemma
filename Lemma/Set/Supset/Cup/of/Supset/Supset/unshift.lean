import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
  {g f : ℤ → Set α}
-- given
  (h₀ : b ≥ a + 1)
  (h₁ : g (a - 1) ⊇ f (a - 1))
  (h₂ : (⋃ k ∈ Finset.Ico a b, g k) ⊇ ⋃ k ∈ Finset.Ico a b, f k) :
-- imply
  (⋃ k ∈ Finset.Ico (a - 1) b, g k) ⊇ ⋃ k ∈ Finset.Ico (a - 1) b, f k := by
-- proof
  have e : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [e, Finset.set_biUnion_insert, Finset.set_biUnion_insert]
  apply Set.union_subset_union h₁ h₂


-- created on 2026-10-11
-- updated on 2026-10-17
