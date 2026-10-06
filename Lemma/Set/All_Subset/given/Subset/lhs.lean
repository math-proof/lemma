import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → Set α}
  {A : Set α}
-- given
  (h : ∀ i ∈ Finset.range n, x i ⊆ A) :
-- imply
  (⋃ i ∈ Finset.range n, x i) ⊆ A := by
-- proof
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
  exact h i hi hzi


-- created on 2020-07-29
