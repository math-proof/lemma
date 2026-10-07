import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma push
  {a b : ℤ}
  {g f : ℤ → Set ℤ}
-- given
  (h₀ : b ≥ a + 1)
  (h₁ : g b ⊆ f b)
  (h₂ : ⋃ k ∈ Finset.Ico a b, g k ⊆ ⋃ k ∈ Finset.Ico a b, f k) :
-- imply
  ⋃ k ∈ Finset.Ico a (b + 1), g k ⊆ ⋃ k ∈ Finset.Ico a (b + 1), f k := by
-- proof
  have e : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [e, Finset.set_biUnion_insert, Finset.set_biUnion_insert]
  exact Set.union_subset_union h₁ h₂


@[main]
private lemma unshift
  {a b : ℤ}
  {g f : ℤ → Set ℤ}
-- given
  (h₀ : b ≥ a + 1)
  (h₁ : g (a - 1) ⊆ f (a - 1))
  (h₂ : ⋃ k ∈ Finset.Ico a b, g k ⊆ ⋃ k ∈ Finset.Ico a b, f k) :
-- imply
  ⋃ k ∈ Finset.Ico (a - 1) b, g k ⊆ ⋃ k ∈ Finset.Ico (a - 1) b, f k := by
-- proof
  have e : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [e, Finset.set_biUnion_insert, Finset.set_biUnion_insert]
  exact Set.union_subset_union h₁ h₂


-- created on 2020-08-02
