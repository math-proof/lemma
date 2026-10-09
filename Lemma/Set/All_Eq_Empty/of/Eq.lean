import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → Finset α}
-- given
  (h : ((Finset.range n).biUnion x).card = ∑ i ∈ Finset.range n, (x i).card) :
-- imply
  ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range i, x i ∩ x j = ∅ := by
-- proof
  intro i hi j hj
  rw [Finset.mem_range] at hi hj
  have hj' : j ∈ (Finset.range n).erase i :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hs : ∑ k ∈ Finset.range n, (x k).card =
      (x i).card + ((x j).card + ∑ k ∈ ((Finset.range n).erase i).erase j, (x k).card) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi), ← Finset.add_sum_erase _ _ hj']
  have hu : (Finset.range n).biUnion x = x i ∪ x j ∪ (((Finset.range n).erase i).erase j).biUnion x := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase, Finset.mem_range]
    constructor
    ·
      rintro ⟨k, hk, ha⟩
      by_cases hki : k = i
      ·
        subst hki
        exact Or.inl (Or.inl ha)
      by_cases hkj : k = j
      ·
        subst hkj
        exact Or.inl (Or.inr ha)
      exact Or.inr ⟨k, ⟨hkj, hki, hk⟩, ha⟩
    ·
      rintro ((ha | ha) | ⟨k, ⟨-, -, hk⟩, ha⟩)
      ·
        exact ⟨i, hi, ha⟩
      ·
        exact ⟨j, by omega, ha⟩
      ·
        exact ⟨k, hk, ha⟩
  have h₁ := Finset.card_union_le (x i ∪ x j) ((((Finset.range n).erase i).erase j).biUnion x)
  have h₂ := Finset.card_biUnion_le (s := ((Finset.range n).erase i).erase j) (t := x)
  have h₃ := Finset.card_union_add_card_inter (x i) (x j)
  rw [hu, hs] at h
  have h₄ : (x i ∩ x j).card = 0 := by
    omega
  exact Finset.card_eq_zero.mp h₄


-- created on 2021-03-19
