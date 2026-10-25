/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4WiredPhaseInput.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem measurableSet_hasInfiniteClusterEvent (d : Nat) :
    MeasurableSet (hasInfiniteClusterEvent d) := by
  exact MeasurableSet.iUnion (fun x => FK.measurableSet_clusterInfiniteEvent x)


theorem percolationProbability_pos_of_hasInfiniteCluster_ae
    {d : Nat} (mu : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure mu]
    (hTI : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu)
    (hglobal : mu (hasInfiniteClusterEvent d) = 1) :
    0 < mu.real (percolationEvent d) := by
  by_contra hnot
  have horigin : mu.real (FK.clusterInfiniteEvent d (origin d)) = 0 := by
    apply le_antisymm (not_lt.mp hnot) measureReal_nonneg
  have hallReal : forall x : Site d,
      mu.real (FK.clusterInfiniteEvent d x) = 0 := by
    intro x
    rw [clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu hTI x,
      horigin]
  have hall : forall x : Site d, mu (FK.clusterInfiniteEvent d x) = 0 := by
    intro x
    exact (measureReal_eq_zero_iff (measure_ne_top mu _)).1 (hallReal x)
  have hzero : mu (hasInfiniteClusterEvent d) = 0 := by
    unfold hasInfiniteClusterEvent
    exact measure_iUnion_null hall
  rw [hglobal] at hzero
  exact one_ne_zero hzero


theorem wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae
    {d : Nat} {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hglobal :
      ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))) (hasInfiniteClusterEvent d) = 1) :
    0 < ((FK.wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d) := by
  apply percolationProbability_pos_of_hasInfiniteCluster_ae _
    (FK.fkgqt_wiredIV_isTranslationInvariant hp hp1 hq)
  exact hglobal


theorem fkQgt4_discontinuity_of_winding_and_positive_order
    {q xiInv : Real} (hq : 4 < q) (hxi : 0 < xiInv)
    (hrate : Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq)
      Filter.atTop (nhds xiInv))
    (hWiredPositive :
      let mu := ((FK.wiredInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))))
      0 < mu.real (percolationEvent 2))
    (hwind : FKQgt4TorusSixVertexWindingBridge xiInv
      (fkQgt4SixVertexGapRate q)) :
    FK.IsFirstOrderTransition 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q)
      ∧ FK.freeInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q) ≠
        FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q)
      ∧ Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop
          (nhds (fkQgt4SixVertexGapRate q))
      ∧ 0 < fkQgt4SixVertexGapRate q := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu0 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have hdecay := fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    hq hxi hrate
  have hfreeTI : forall x : Site 2,
      mu0.real (FK.clusterInfiniteEvent 2 x) =
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) := by
    intro x
    apply clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu0
    simpa [mu0] using
      (FK.fkgqt_freeIV_isTranslationInvariant (d := 2) hp hp1 hq1)
  have hfreeUniq : mu0 (atLeastTwoInfinite 2) = 0 := by
    have h := (FK.freeInfinite_canonical_uniqueness_all_parameters
      (d := 2) (by norm_num) hp hp1 hq1).2.1
    simpa [mu0] using h
  have hFree : FK.fkThetaFree 2 hp hp1 hq0 (q := q) = 0 := by
    change mu0.real (percolationEvent 2) = 0
    have hfreePA : forall x : Site 2,
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) *
            mu0.real (FK.clusterInfiniteEvent 2 x) <=
          mu0.real (FK.clusterInfiniteEvent 2 (origin 2) ∩
            FK.clusterInfiniteEvent 2 x) := by
      intro x
      simpa [mu0] using FK.fkgq_freeInfiniteVolume_clusterInfinite_fkg
        hp hp1 hq1 (origin 2) x
    exact percolationProbability_eq_zero_of_twoPoint_tendsto_zero
      mu0 hfreePA hfreeTI hfreeUniq
      (fun n => fkQgt4DiagonalSite (n + 1)) hdecay
  have horder := FK.order_transition_q_large_selfDual hq hFree hWiredPositive
  have hrateEq := fkQgt4_inverseCorrelation_eq_sixVertexGapRate hwind.toBounds
  have hrateGap : Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop
      (nhds (fkQgt4SixVertexGapRate q)) := by
    rwa [← hrateEq]
  have hgapPos : 0 < fkQgt4SixVertexGapRate q := by
    rwa [← hrateEq]
  exact ⟨horder.1, horder.2, hrateGap, hgapPos⟩


theorem fkQgt4_discontinuity_of_winding_and_global_wired_order
    {q xiInv : Real} (hq : 4 < q) (hxi : 0 < xiInv)
    (hrate : Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq)
      Filter.atTop (nhds xiInv))
    (hglobal :
      ((FK.wiredInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1)
    (hwind : FKQgt4TorusSixVertexWindingBridge xiInv
      (fkQgt4SixVertexGapRate q)) :
    FK.IsFirstOrderTransition 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q)
      ∧ FK.freeInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q) ≠
        FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q)
      ∧ Filter.Tendsto (fkQgt4CriticalFreeDiagonalRate hq) Filter.atTop
          (nhds (fkQgt4SixVertexGapRate q))
      ∧ 0 < fkQgt4SixVertexGapRate q := by
  apply fkQgt4_discontinuity_of_winding_and_positive_order hq hxi hrate
    (wiredInfiniteVolume_percolationEvent_pos_of_hasInfiniteCluster_ae
      (d := 2)
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (1 : Real) <= q) hglobal)
    hwind

end
end StatMech.FrontierD
