import Mathlib.Probability.ConditionalProbability
import sympy.Basic
open MeasureTheory ProbabilityTheory Set


/--
Negative-prompt Bayes: if `C ⊆ A` and `B` is the rejected event, then
`P(C | A ∩ Bᶜ) = P(C) (1 - P(B | C)) / P(A ∩ Bᶜ)`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {A B C : Set Ω}
-- given
  (h₀ : MeasurableSet A)
  (h₁ : MeasurableSet B)
  (h₂ : MeasurableSet C)
  (h₃ : C ⊆ A)
  (h₄ : π (A ∩ Bᶜ) ≠ 0)
  (h₅ : π C ≠ 0) :
-- imply
  (π[|A ∩ Bᶜ]).real C = π.real C * (1 - (π[|C]).real B) / π.real (A ∩ Bᶜ) := by
-- proof
  have htop : ∀ s, π s ≠ ⊤ := fun s => measure_ne_top π s
  have hAC : (A ∩ Bᶜ) ∩ C = C ∩ Bᶜ := by
    ext x
    constructor
    ·
      rintro ⟨⟨_, hxB⟩, hxC⟩
      exact ⟨hxC, hxB⟩
    ·
      rintro ⟨hxC, hxB⟩
      exact ⟨⟨h₃ hxC, hxB⟩, hxC⟩
  have hdis : Disjoint (C ∩ Bᶜ) (C ∩ B) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.1.2 hx.2.2
  have hunion : (C ∩ Bᶜ) ∪ (C ∩ B) = C := by
    ext x
    constructor
    ·
      intro hx
      cases hx with
      | inl hx => exact hx.1
      | inr hx => exact hx.1
    ·
      intro hxC
      if hxB : x ∈ B then
        exact Or.inr ⟨hxC, hxB⟩
      else
        exact Or.inl ⟨hxC, hxB⟩
  have hsub : π (C ∩ Bᶜ) = π C - π (C ∩ B) := by
    have hmu : π ((C ∩ Bᶜ) ∪ (C ∩ B)) = π (C ∩ Bᶜ) + π (C ∩ B) :=
      measure_union hdis (h₂.inter h₁)
    rw [hunion] at hmu
    rw [hmu]
    exact (ENNReal.add_sub_cancel_right (htop _)).symm
  rw [measureReal_def, measureReal_def, measureReal_def, cond_apply (h₀.inter h₁.compl),
    cond_apply h₂, hAC, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul,
    ENNReal.toReal_inv, hsub,
    ENNReal.toReal_sub_of_le (measure_mono (Set.inter_subset_left (s := C))) (htop _)]
  have hposC : (π C).toReal ≠ 0 := (ENNReal.toReal_pos h₅ (htop _)).ne'
  have hposA : (π (A ∩ Bᶜ)).toReal ≠ 0 := (ENNReal.toReal_pos h₄ (htop _)).ne'
  simp only [measureReal_def]
  field_simp [hposC, hposA]


-- created on 2024-06-20
-- updated on 2026-10-17
