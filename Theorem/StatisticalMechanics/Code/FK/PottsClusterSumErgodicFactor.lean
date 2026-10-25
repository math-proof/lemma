/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part10
import Def.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor
open MeasureTheory Set


namespace StatMech.FK

theorem IsErgodicFor.map
    {G Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    {sourceShift : G -> Omega -> Omega} {targetShift : G -> Xi -> Xi}
    {mu : Measure Omega} (hergodic : IsErgodicFor sourceShift mu)
    (factor : Omega -> Xi) (hfactor : Measurable factor)
    (htarget : ∀ g, Measurable (targetShift g))
    (hequivariant : ∀ g omega,
      factor (sourceShift g omega) = targetShift g (factor omega)) :
    IsErgodicFor targetShift (Measure.map factor mu) := by
  refine ⟨?_, ?_⟩
  · intro g
    refine ⟨htarget g, ?_⟩
    rw [Measure.map_map (htarget g) hfactor]
    have hcomp : targetShift g ∘ factor = factor ∘ sourceShift g := by
      funext omega
      exact (hequivariant g omega).symm
    rw [hcomp, ← Measure.map_map hfactor (hergodic.1 g).measurable,
      (hergodic.1 g).map_eq]
  · intro s hs hinvariant
    have hpre : MeasurableSet (factor ⁻¹' s) := hs.preimage hfactor
    have hpreInvariant : ∀ g, sourceShift g ⁻¹' (factor ⁻¹' s) =
        factor ⁻¹' s := by
      intro g
      ext omega
      simp only [Set.mem_preimage]
      rw [hequivariant g omega]
      exact Set.ext_iff.mp (hinvariant g) (factor omega)
    rcases hergodic.2 (factor ⁻¹' s) hpre hpreInvariant with hzero | hfull
    · left
      rw [Measure.map_apply hfactor hs, hzero]
    · right
      rw [Measure.map_apply hfactor hs,
        Measure.map_apply hfactor MeasurableSet.univ,
        Set.preimage_univ, hfull]


end StatMech.FK
