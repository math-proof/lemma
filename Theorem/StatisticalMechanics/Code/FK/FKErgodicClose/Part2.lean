/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Mathlib
import Def.StatisticalMechanics.Code.FK.FKErgodicClose
open MeasureTheory ProbabilityTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


theorem fec_isErgodic_of_invariantExtremePoint {μ : Measure (ConfigSpace E)}
    (hμ : IsInvariantExtremePoint (G := G) μ) :
    IsErgodic (G := G) μ := by
  obtain ⟨hinvμ, hprobμ, hext⟩ := hμ
  haveI : IsProbabilityMeasure μ := hprobμ
  refine ⟨hinvμ, ?_⟩
  intro s hs hinv
  
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hs0, hs1⟩ := hcon
  rw [measure_univ] at hs1
  
  have hsc0 : μ sᶜ ≠ 0 := by
    intro h
    apply hs1
    have : μ s + μ sᶜ = 1 := by
      rw [← measure_univ (μ := μ)]
      exact (measure_add_measure_compl hs)
    rw [h, add_zero] at this
    exact this
  
  have hinvc : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  
  haveI hp1 : IsProbabilityMeasure (μ[|s]) := cond_isProbabilityMeasure hs0
  haveI hp2 : IsProbabilityMeasure (μ[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hti1 : IsTranslationInvariant (G := G) (μ[|s]) :=
    fec_cond_isTranslationInvariant hinvμ hs hinv
  have hti2 : IsTranslationInvariant (G := G) (μ[|sᶜ]) :=
    fec_cond_isTranslationInvariant hinvμ hs.compl hinvc
  
  have hab : μ s + μ sᶜ = 1 := by
    rw [← measure_univ (μ := μ)]; exact measure_add_measure_compl hs
  have hapos : 0 < μ s := pos_iff_ne_zero.mpr hs0
  have hbpos : 0 < μ sᶜ := pos_iff_ne_zero.mpr hsc0
  have hdecomp : μ = (μ s) • (μ[|s]) + (μ sᶜ) • (μ[|sᶜ]) :=
    fec_invariant_decomp hs hs0 hsc0
  
  have heq : (μ[|s]) = (μ[|sᶜ]) :=
    hext (μ[|s]) (μ[|sᶜ]) (μ s) (μ sᶜ) hti1 hti2 hp1 hp2 hapos hbpos hab hdecomp
  
  have hval1 : (μ[|s]) s = 1 := cond_apply_self hs0 (measure_ne_top μ s)
  have hval2 : (μ[|sᶜ]) s = 0 := by
    rw [cond_apply hs.compl, Set.inter_comm, Set.inter_compl_self, measure_empty,
      mul_zero]
  rw [heq] at hval1
  rw [hval1] at hval2
  exact one_ne_zero hval2


theorem fec_wiredIV_isErgodic_of_extremePoint {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hext : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  refine fec_isErgodic_of_invariantExtremePoint
    ⟨flc_wiredIV_isTranslationInvariant hp hp1, ?_, hext⟩
  infer_instance


theorem fec_freeIV_isErgodic_of_extremePoint {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (htifree : IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))))
    (hext : ∀ (ν₁ ν₂ : Measure (ConfigSpace (Sym2 (Site d)))) (a b : ℝ≥0∞),
      IsTranslationInvariant (G := Multiplicative (Site d)) ν₁ →
        IsTranslationInvariant (G := Multiplicative (Site d)) ν₂ →
          IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
            0 < a → 0 < b → a + b = 1 →
              (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
                : Measure (ConfigSpace (Sym2 (Site d)))) = a • ν₁ + b • ν₂ → ν₁ = ν₂) :
    IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  refine fec_isErgodic_of_invariantExtremePoint ⟨htifree, ?_, hext⟩
  infer_instance

end FK
end StatMech
