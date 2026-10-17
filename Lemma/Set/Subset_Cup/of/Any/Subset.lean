import sympy.Basic


@[path]
private lemma main
  {a : α}
  {f : ι → Set α}
-- given
  (h₀ : ({a} : Set α) ⊆ ⋃ i, f i) :
-- imply
  ∃ i, ({a} : Set α) ⊆ f i := by
-- proof
  have ha : a ∈ ⋃ i, f i := h₀ (Set.mem_singleton a)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
  exact ⟨i, fun x hx => by simpa [Set.mem_singleton_iff.mp hx] using hi⟩


-- created on 2026-10-11
-- updated on 2026-10-17
