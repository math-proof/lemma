import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {t : ℕ}
  {A L : ℕ → ℕ → ℂ}
-- given
  (h : ∀ i < t, L t i = (A t i - ∑ k ∈ Finset.range i, L t k * ~(L i k)) / L i i ∧ L i i ∈ Complex.ofReal '' Set.Ioi 0 ∧ ∀ j < i, L i j ∈ (Set.univ : Set ℂ)) :
-- imply
  ∀ j < t, L t j ∈ (Set.univ : Set ℂ) ∧ A t j = ∑ k ∈ Finset.range (j + 1), L t k * ~(L j k) := by
-- proof
  intro j hj
  obtain ⟨h₁, ⟨r, hr, hL⟩, -⟩ := h j hj
  refine ⟨Set.mem_univ _, ?_⟩
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  rw [Finset.sum_range_succ, h₁, ← hL]
  simp only [Complex.conj_ofReal]
  field_simp
  ring


@[main]
private lemma real
  {t : ℕ}
  {A L : ℕ → ℕ → ℝ}
-- given
  (h : ∀ i < t, L t i = (A t i - ∑ k ∈ Finset.range i, L t k * L i k) / L i i ∧ L i i ∈ Set.Ioi 0 ∧ ∀ j < i, L i j ∈ (Set.univ : Set ℝ)) :
-- imply
  ∀ j < t, L t j ∈ (Set.univ : Set ℝ) ∧ A t j = ∑ k ∈ Finset.range (j + 1), L t k * L j k := by
-- proof
  intro j hj
  obtain ⟨h₁, hL, -⟩ := h j hj
  refine ⟨Set.mem_univ _, ?_⟩
  have hL' : L j j ≠ 0 := ne_of_gt hL
  rw [Finset.sum_range_succ, h₁]
  field_simp
  ring


-- created on 2023-06-05
