/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TIChoquetClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.GibbsChoquet.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem tic_trim_restrict_comm {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (μ : @Measure Ω mΩ) (hm : m ≤ mΩ) (s : Set Ω) (hs : @MeasurableSet Ω m s) :
    @Measure.trim Ω m mΩ (@Measure.restrict Ω mΩ μ s) hm
      = @Measure.restrict Ω m (@Measure.trim Ω m mΩ μ hm) s := by
  apply @Measure.ext Ω m
  intro t ht
  rw [@trim_measurableSet_eq Ω m mΩ _ t hm ht,
    @Measure.restrict_apply Ω m (@Measure.trim Ω m mΩ μ hm) s t ht,
    @Measure.restrict_apply Ω mΩ μ s t (hm t ht),
    @trim_measurableSet_eq Ω m mΩ μ (t ∩ s) hm (ht.inter hs)]


theorem tic_compProd_restrict_left {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : @Measure α mα) [SFinite μ] (K : @Kernel α β mα mβ) [IsSFiniteKernel K]
    (s : Set α) (hs : MeasurableSet s) :
    (μ.restrict s) ⊗ₘ K = (μ ⊗ₘ K).restrict (s ×ˢ Set.univ) := by
  apply Measure.ext
  intro t ht
  rw [Measure.compProd_apply ht, Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    ← lintegral_indicator hs]
  congr 1
  funext a
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
    congr 1
    ext b
    simp [ha]
  · rw [Set.indicator_of_notMem ha]
    have hempty : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = ∅ := by
      ext b; simp [ha]
    rw [hempty, measure_empty]


theorem tic_map_diag_restrict {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    (μ : @Measure Ω mΩ) (s : Set Ω) (hs : @MeasurableSet Ω m s)
    (hf : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω => (id ω, id ω))) :
    @Measure.restrict (Ω × Ω) (m.prod mΩ)
        (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) (s ×ˢ Set.univ)
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω))
          (@Measure.restrict Ω mΩ μ s) := by
  apply @Measure.ext (Ω × Ω) (m.prod mΩ)
  intro t ht
  rw [@Measure.restrict_apply (Ω × Ω) (m.prod mΩ) _ (s ×ˢ Set.univ) t ht,
    @Measure.map_apply Ω (Ω × Ω) mΩ (m.prod mΩ) μ _ hf _ (ht.inter ((hs.prod MeasurableSet.univ))),
    @Measure.map_apply Ω (Ω × Ω) mΩ (m.prod mΩ) (@Measure.restrict Ω mΩ μ s) _ hf t ht,
    @Measure.restrict_apply Ω mΩ μ s _ (hf ht)]
  congr 1
  ext ω
  simp


end Ising
end StatMech
