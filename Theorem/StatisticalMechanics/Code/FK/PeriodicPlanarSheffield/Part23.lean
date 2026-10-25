/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


namespace PeriodicPlanarDualPair

theorem commonUniqueInfiniteClusterEvent_measurableSet
    (D : PeriodicPlanarDualPair P Pdual) :
    MeasurableSet D.commonUniqueInfiniteClusterEvent :=
  P.measurableSet_hasUniqueInfiniteCluster.inter
    (Pdual.measurableSet_hasUniqueInfiniteCluster.preimage
      (continuous_dualConfigEquiv D.edgeDual).measurable)

theorem commonUniqueInfiniteClusterEvent_translate_preimage
    (D : PeriodicPlanarDualPair P Pdual) (z : Site 2) :
    P.configTranslate z ⁻¹' D.commonUniqueInfiniteClusterEvent =
      D.commonUniqueInfiniteClusterEvent := by
  ext omega
  simp only [commonUniqueInfiniteClusterEvent, Set.mem_preimage,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [P.hasUniqueInfiniteCluster_configTranslate,
    D.dualConfigEquiv_configTranslate,
    Pdual.hasUniqueInfiniteCluster_configTranslate]

theorem commonUniqueInfiniteClusterEvent_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
    mu D.commonUniqueInfiniteClusterEvent = 1 := by
  let A := {omega : ConfigSpace (Sym2 V) |
    P.HasUniqueInfiniteCluster omega}
  let B := (dualConfigEquiv D.edgeDual) ⁻¹'
    {eta | Pdual.HasUniqueInfiniteCluster eta}
  have hAmeas : MeasurableSet A :=
    P.measurableSet_hasUniqueInfiniteCluster
  have hBmeas : MeasurableSet B :=
    Pdual.measurableSet_hasUniqueInfiniteCluster.preimage
      (continuous_dualConfigEquiv D.edgeDual).measurable
  have hAc : mu Aᶜ = 0 := (prob_compl_eq_zero_iff hAmeas).2 hprimal
  have hBc : mu Bᶜ = 0 := (prob_compl_eq_zero_iff hBmeas).2 hdual
  have hinterc : mu (A ∩ B)ᶜ = 0 := by
    rw [compl_inter]
    exact MeasureTheory.measure_union_null hAc hBc
  change mu (A ∩ B) = 1
  simpa using MeasureTheory.measure_of_measure_compl_eq_zero hinterc

theorem exists_primal_dual_fundamental_clusterInfinite_pos
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
    (∃ u ∈ P.fundamentalDomain,
      0 < mu {omega | (P.cluster omega u).Infinite}) ∧
    (∃ w ∈ Pdual.fundamentalDomain,
      0 < D.dualMeasure mu
        {eta | (Pdual.cluster eta w).Infinite}) := by
  have hprimalExists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hprimal]
    exact measure_mono fun omega h => h.1
  have hleft := P.exists_fundamental_clusterInfinite_pos
    mu hTI hprimalExists
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  have hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
    unfold dualMeasure
    rw [Measure.map_apply
      (continuous_dualConfigEquiv D.edgeDual).measurable
      Pdual.measurableSet_hasUniqueInfiniteCluster]
    exact hdual
  have hdualExists : D.dualMeasure mu
      {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hdualUnique]
    exact measure_mono fun eta h => h.1
  have hright := Pdual.exists_fundamental_clusterInfinite_pos
    (D.dualMeasure mu) (D.dualMeasure_isTranslationInvariant mu hTI)
      hdualExists
  exact ⟨hleft, hright⟩

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
