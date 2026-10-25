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
open MeasureTheory ProbabilityTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


theorem fec_restrict_measurePreserving {μ : Measure (ConfigSpace E)}
    (hμ : IsTranslationInvariant (G := G) μ) (g : G)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E)
      (μ.restrict s) (μ.restrict s) := by
  have h := (hμ g).restrict_preimage hs
  rwa [hinv] at h


theorem fec_cond_isTranslationInvariant {μ : Measure (ConfigSpace E)}
    (hμ : IsTranslationInvariant (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    IsTranslationInvariant (G := G) (μ[|s]) := by
  intro g
  
  have hrestr := fec_restrict_measurePreserving hμ g hs (hinv g)
  refine ⟨measurable_shift g, ?_⟩
  rw [ProbabilityTheory.cond]
  rw [Measure.map_smul]
  rw [hrestr.map_eq]


theorem fec_invariant_decomp {μ : Measure (ConfigSpace E)} [IsFiniteMeasure μ]
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hs0 : μ s ≠ 0) (hsc0 : μ sᶜ ≠ 0) :
    μ = (μ s) • (μ[|s]) + (μ sᶜ) • (μ[|sᶜ]) := by
  have hstop : μ s ≠ ∞ := measure_ne_top μ s
  have hsctop : μ sᶜ ≠ ∞ := measure_ne_top μ sᶜ
  
  have h1 : (μ s) • (μ[|s]) = μ.restrict s := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hs0 hstop, one_smul]
  have h2 : (μ sᶜ) • (μ[|sᶜ]) = μ.restrict sᶜ := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hsc0 hsctop, one_smul]
  rw [h1, h2, Measure.restrict_add_restrict_compl hs]


end FK
end StatMech
