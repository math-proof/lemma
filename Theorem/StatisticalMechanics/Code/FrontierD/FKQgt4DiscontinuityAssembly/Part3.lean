/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CorrelationReduction
import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQClusterFKG
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Structure.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem FKQgt4TorusSixVertexWindingBridge.toBounds
    {xiInv R : Real} (h : FKQgt4TorusSixVertexWindingBridge xiInv R) :
    FKQgt4WindingSectorBounds xiInv R :=
  ⟨h.oneWinding, h.fixedCharge⟩


theorem fkQgt4_discontinuity_of_winding_and_order_inputs
    {q xiInv : Real} (hq : 4 < q) (hxi : 0 < xiInv)
    (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds xiInv))
    (hWiredAlmostSure :
      let mu := ((FK.wiredInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))) )
      mu (percolationEvent 2) = 1)
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
      ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
        (nhds (fkQgt4SixVertexGapRate q))
      ∧ 0 < fkQgt4SixVertexGapRate q
      ∧ (((FK.wiredInfiniteVolume 2
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
          (by linarith : (0 : Real) < q) :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
          Measure (ConfigSpace (Sym2 (Site 2))))
        (percolationEvent 2) = 1) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  have hq1 : (1 : Real) ≤ q := by linarith
  let mu0 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  let mu1 : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.wiredInfiniteVolume 2 hp hp1 hq0
  have hdecay := fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate
    hq hxi hrate
  have hfreeTI : ∀ x : Site 2,
      mu0.real (FK.clusterInfiniteEvent 2 x) =
        mu0.real (FK.clusterInfiniteEvent 2 (origin 2)) := by
    intro x
    apply clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu0
    simpa [mu0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
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
  have hWired : 0 < FK.fkTheta 2 hp hp1 hq0 (q := q) := by
    change 0 < mu1.real (percolationEvent 2)
    unfold Measure.real
    rw [hWiredAlmostSure]
    norm_num
  have horder := FK.order_transition_q_large_selfDual hq hFree hWired
  have hrateEq := fkQgt4_inverseCorrelation_eq_sixVertexGapRate hwind.toBounds
  have hrateGap : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop
      (nhds (fkQgt4SixVertexGapRate q)) := by
    rwa [<- hrateEq]
  have hgapPos : 0 < fkQgt4SixVertexGapRate q := by
    rwa [<- hrateEq]
  exact ⟨horder.1, horder.2, hrateGap, hgapPos, hWiredAlmostSure⟩

end
end StatMech.FrontierD
