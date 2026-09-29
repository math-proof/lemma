import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-- If finsets `w i` (`i < k`) have total size `|⋃ w i|`, they are pairwise disjoint. -/
theorem Finset.eq_of_mem_of_sum_card_eq {w : ℕ → Finset ℕ} {k M : ℕ}
    (h₀ : ∑ i ∈ Finset.range k, (w i).card = M) (h₁ : (Finset.range k).biUnion w = Finset.range M)
    {j i1 i2 : ℕ} (hi1 : i1 < k) (hi2 : i2 < k) (hj1 : j ∈ w i1) (hj2 : j ∈ w i2) : i1 = i2 := by
  by_contra hne
  have m1 : i1 ∈ Finset.range k := Finset.mem_range.mpr hi1
  have m2 : i2 ∈ (Finset.range k).erase i1 := Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_range.mpr hi2⟩
  set rest := ((Finset.range k).erase i1).erase i2
  have hsum : ∑ i ∈ Finset.range k, (w i).card = (w i1).card + ((w i2).card + ∑ i ∈ rest, (w i).card) := by
    rw [← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
  have hsub : (Finset.range k).biUnion w ⊆ (w i1 ∪ w i2) ∪ rest.biUnion w := by
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_union, rest, Finset.mem_erase] at hy ⊢
    obtain ⟨i, hi, hy⟩ := hy
    by_cases e1 : i = i1
    · subst e1
      exact Or.inl (Or.inl hy)
    by_cases e2 : i = i2
    · subst e2
      exact Or.inl (Or.inr hy)
    exact Or.inr ⟨i, ⟨e2, e1, hi⟩, hy⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (w i1 ∪ w i2) (rest.biUnion w)
  have h3 := Finset.card_biUnion_le (s := rest) (t := w)
  have h4 := Finset.card_union_add_card_inter (w i1) (w i2)
  have h5 : 0 < (w i1 ∩ w i2).card := Finset.card_pos.mpr ⟨j, Finset.mem_inter.mpr ⟨hj1, hj2⟩⟩
  rw [h₁, Finset.card_range] at h1
  omega


-- created on 2026-09-27
