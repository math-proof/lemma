/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWBxpAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Instance.StatisticalMechanics.Code.Universality.RSWBxpAssembly
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem rba_measurable_dualConfig :
    Measurable (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
  rw [dualConfig_eq_comp]
  exact measurable_complement.comp measurable_reindex


theorem rba_dualVerticalCrossing_eq (a b c d : ℤ)
    (hmeasV : MeasurableSet (verticalCrossingEvent a b c d)) :
    rba_selfDualMeasure.real (dualVerticalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
  have hpre : dualVerticalCrossingEvent a b c d
      = dualConfig ⁻¹' verticalCrossingEvent a b c d := rfl
  unfold rba_selfDualMeasure
  rw [hpre, Measure.real, ← Measure.map_apply rba_measurable_dualConfig hmeasV,
    bernoulliProductMeasure_selfDual_half]
  rfl


theorem rba_dualHorizontalCrossing_eq (a b c d : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent a b c d)) :
    rba_selfDualMeasure.real (dualHorizontalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  have hpre : dualHorizontalCrossingEvent a b c d
      = dualConfig ⁻¹' horizontalCrossingEvent a b c d := rfl
  unfold rba_selfDualMeasure
  rw [hpre, Measure.real, ← Measure.map_apply rba_measurable_dualConfig hmeasH,
    bernoulliProductMeasure_selfDual_half]
  rfl


theorem rba_self_dual_square_half (n : ℤ)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hsep : (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n)
    (hsqsym : rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n)
                = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
  have hselfDual : rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n)
      = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [rba_dualVerticalCrossing_eq 0 n 0 n hmeasV, hsqsym]
  have hcompl : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      = 1 - rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
    rw [measureReal_compl hmeasH, probReal_univ]
  have hmono : rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n)ᶜ
      ≤ rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n) :=
    measureReal_mono hsep
  rw [hselfDual, hcompl] at hmono
  linarith


theorem rba_glued_rectangle_lower_bound
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ} {v0 : ℝ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    (hL : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent a m' c d))
    (hR : (1 : ℝ) / 2 ≤ μ.real (horizontalCrossingEvent m b c d))
    (hVlb : v0 ≤ μ.real (verticalCrossingEvent m m' c d)) (hv0 : 0 ≤ v0) :
    v0 / 4 ≤ μ.real (horizontalCrossingEvent a b c d) := by
  have hglue := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  set HL := μ.real (horizontalCrossingEvent a m' c d) with hHL
  set HR := μ.real (horizontalCrossingEvent m b c d) with hHR
  set V := μ.real (verticalCrossingEvent m m' c d) with hVdef
  have hLnn : (0 : ℝ) ≤ HL := measureReal_nonneg
  have h1 : (1 / 2 : ℝ) * v0 ≤ HL * V := mul_le_mul hL hVlb hv0 hLnn
  have h2 : ((1 / 2 : ℝ) * v0) * (1 / 2) ≤ HL * V * HR :=
    mul_le_mul h1 hR (by norm_num) (by positivity)
  have hprod : v0 / 4 ≤ HL * V * HR := by nlinarith [h2]
  linarith [hglue, hprod]


theorem rba_bxp_of_uniform_seed
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    (ρ : ℝ) (hρ : 1 < ρ) (n0 : ℕ) (c : ℝ) (hc : 0 < c)
    (hH : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n →
      c ≤ μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)))
    (hV : ∀ (n : ℕ) (τ : Site 2), n0 ≤ n →
      c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋)) :
    BoxCrossingProperty μ ρ := by
  refine ⟨hρ, n0, ?_⟩
  have hlb : ∀ x ∈ boxCrossingProbabilities μ ρ n0, c ≤ x := by
    rintro x ⟨n, τ, hn, rfl | rfl⟩
    · exact hH n τ hn
    · exact hV n τ hn
  have hne : (boxCrossingProbabilities μ ρ n0).Nonempty :=
    ⟨μ.real (translatedHorizontalCrossingEvent 0 ⌊ρ * (n0 : ℝ)⌋ (n0 : ℤ)),
      n0, 0, le_refl _, Or.inl rfl⟩
  have hge : c ≤ sInf (boxCrossingProbabilities μ ρ n0) := le_csInf hne hlb
  rw [boxCrossingInf]; linarith

end Universality
end StatMech
