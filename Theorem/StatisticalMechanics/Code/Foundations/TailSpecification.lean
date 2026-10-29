/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]


theorem ts_trim_restrict_comm {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (hm : m ≤ mOmega)
    (s : Set Omega) (hs : @MeasurableSet Omega m s) :
    @Measure.trim Omega m mOmega (@Measure.restrict Omega mOmega mu s) hm =
      @Measure.restrict Omega m (@Measure.trim Omega m mOmega mu hm) s := by
  apply @Measure.ext Omega m
  intro t ht
  rw [@trim_measurableSet_eq Omega m mOmega _ t hm ht,
    @Measure.restrict_apply Omega m (@Measure.trim Omega m mOmega mu hm) s t ht,
    @Measure.restrict_apply Omega mOmega mu s t (hm t ht),
    @trim_measurableSet_eq Omega m mOmega mu (t ∩ s) hm (ht.inter hs)]

theorem ts_compProd_restrict_left {alpha beta : Type*}
    {mAlpha : MeasurableSpace alpha} {mBeta : MeasurableSpace beta}
    (mu : @Measure alpha mAlpha) [SFinite mu]
    (K : @Kernel alpha beta mAlpha mBeta) [IsSFiniteKernel K]
    (s : Set alpha) (hs : MeasurableSet s) :
    (mu.restrict s) ⊗ₘ K = (mu ⊗ₘ K).restrict (s ×ˢ Set.univ) := by
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
      ext b
      simp [ha]
    rw [hempty, measure_empty]

theorem ts_map_diag_restrict {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (s : Set Omega)
    (hs : @MeasurableSet Omega m s)
    (hf : @Measurable Omega (Omega × Omega) mOmega (m.prod mOmega)
      (fun omega => (id omega, id omega))) :
    @Measure.restrict (Omega × Omega) (m.prod mOmega)
        (@Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega)
          (fun omega => (id omega, id omega)) mu) (s ×ˢ Set.univ) =
      @Measure.map Omega (Omega × Omega) mOmega (m.prod mOmega)
        (fun omega => (id omega, id omega))
        (@Measure.restrict Omega mOmega mu s) := by
  apply @Measure.ext (Omega × Omega) (m.prod mOmega)
  intro t ht
  rw [@Measure.restrict_apply (Omega × Omega) (m.prod mOmega) _
      (s ×ˢ Set.univ) t ht,
    @Measure.map_apply Omega (Omega × Omega) mOmega (m.prod mOmega) mu _ hf _
      (ht.inter (hs.prod MeasurableSet.univ)),
    @Measure.map_apply Omega (Omega × Omega) mOmega (m.prod mOmega)
      (@Measure.restrict Omega mOmega mu s) _ hf t ht,
    @Measure.restrict_apply Omega mOmega mu s _ (hf ht)]
  congr 1
  ext omega
  simp

theorem ts_trim_smul {Omega : Type*}
    {m mOmega : MeasurableSpace Omega}
    (mu : @Measure Omega mOmega) (hm : m ≤ mOmega) (a : ENNReal) :
    (a • mu).trim hm = a • (mu.trim hm) :=
  @Measure.ext _ m _ _ (fun s hs => by
    rw [Measure.smul_apply, trim_measurableSet_eq hm hs,
      trim_measurableSet_eq hm hs, Measure.smul_apply])


end StatMech
