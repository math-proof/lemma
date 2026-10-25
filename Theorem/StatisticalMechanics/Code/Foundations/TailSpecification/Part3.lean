/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Def.StatisticalMechanics.Code.Foundations.TailSpecification.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]


theorem ts_isErgodic_of_extreme
    {H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (window : ℕ → Set E) (hwindow : Monotone window)
    (hescape : ∀ (F : Finset E) (k : ℕ), ∃ g : H,
      (↑(F.image (fun e => g⁻¹ • e)) : Set E) ⊆ (window k)ᶜ)
    {K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance}
    [∀ n, IsSFiniteKernel (K n)]
    {mu : Measure (ConfigSpace E)} [IsProbabilityMeasure mu]
    (hti : IsTranslationInvariant (G := H) mu)
    (hstate : IsTailSpecificationState window K mu)
    (hext : ∀ (nu₁ nu₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞),
      IsProbabilityMeasure nu₁ → IsProbabilityMeasure nu₂ →
      IsTailSpecificationMeasure window K nu₁ →
      IsTailSpecificationMeasure window K nu₂ →
      0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ →
      mu = a • nu₁ + b • nu₂ → nu₁ = nu₂) :
    IsErgodic (G := H) mu := by
  refine ⟨hti, ?_⟩
  intro s hs hinv
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hs0, hsfull⟩ := hcon
  rw [measure_univ] at hsfull
  have hab : mu s + mu sᶜ = 1 := by
    calc
      mu s + mu sᶜ = mu Set.univ := measure_add_measure_compl hs
      _ = 1 := measure_univ
  have hsc0 : mu sᶜ ≠ 0 := fun hzero =>
    hsfull (by rw [hzero, add_zero] at hab; exact hab)
  have hinvc : ∀ g : H, shift g ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  obtain ⟨t, ht, hst⟩ :=
    ati_invariant_aeTail window hwindow hescape hti s hs hinv
  obtain ⟨u, hu, hscu⟩ :=
    ati_invariant_aeTail window hwindow hescape hti sᶜ hs.compl hinvc
  haveI hp₁ : IsProbabilityMeasure (mu[|s]) := cond_isProbabilityMeasure hs0
  haveI hp₂ : IsProbabilityMeasure (mu[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hstate₁ : IsTailSpecificationState window K (mu[|s]) :=
    ts_cond_state_of_ae_tail mu hstate ht hst hs0
  have hstate₂ : IsTailSpecificationState window K (mu[|sᶜ]) :=
    ts_cond_state_of_ae_tail mu hstate hu hscu hsc0
  have hdecomp : mu = (mu s) • (mu[|s]) + (mu sᶜ) • (mu[|sᶜ]) := by
    have h₁ : (mu s) • (mu[|s]) = mu.restrict s := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hs0 (measure_ne_top mu s), one_smul]
    have h₂ : (mu sᶜ) • (mu[|sᶜ]) = mu.restrict sᶜ := by
      rw [ProbabilityTheory.cond, smul_smul,
        ENNReal.mul_inv_cancel hsc0 (measure_ne_top mu sᶜ), one_smul]
    rw [h₁, h₂, Measure.restrict_add_restrict_compl hs]
  have heq : (mu[|s]) = (mu[|sᶜ]) :=
    hext (mu[|s]) (mu[|sᶜ]) (mu s) (mu sᶜ) hp₁ hp₂
      ⟨inferInstance, hstate₁⟩ ⟨inferInstance, hstate₂⟩
      (pos_iff_ne_zero.mpr hs0) (pos_iff_ne_zero.mpr hsc0) hab
      (measure_ne_top mu s) (measure_ne_top mu sᶜ) hdecomp
  have hval₁ : (mu[|s]) s = 1 :=
    cond_apply_self hs0 (measure_ne_top mu s)
  have hval₂ : (mu[|sᶜ]) s = 0 := by
    rw [cond_apply hs.compl, Set.inter_comm, Set.inter_compl_self,
      measure_empty, mul_zero]
  rw [heq, hval₂] at hval₁
  exact one_ne_zero hval₁.symm

end StatMech
