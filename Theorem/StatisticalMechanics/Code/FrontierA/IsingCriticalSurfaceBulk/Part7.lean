/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part7
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

set_option maxHeartbeats 800000 in


theorem oddPrismUnequalGlue_plus_partition
    (beta : Real) (n : Nat) :
    ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
        (Sum.elim
          (fun v : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n v.1)
          (fun v : OddPrismUpperBlockSite n =>
            beta * oddPrismPlusField n v.1)) =
      scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismPlusField n) beta := by
  classical
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  have h := ghsi_ZJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))
    (fun v => beta * oddPrismPlusField n v) (by
      intro v
      rcases v with v | v <;> rfl)
  calc
    _ = ZJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) := h
    _ = _ := by
      unfold scaledInhomogeneousPartition
      rw [oddPrismInternalGraph_edgeFinset]
      simp only [mul_one]

set_option maxHeartbeats 800000 in


theorem oddPrismUnequalGlue_dobrushin_partition
    (beta : Real) (n : Nat) :
    ZJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
        (Sum.elim
          (fun v : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n v.1)
          (fun v : OddPrismUpperBlockSite n =>
            -(beta * oddPrismPlusField n v.1))) =
      scaledInhomogeneousPartition (oddPrismInternalEdges n) (fun _ => 1)
        (oddPrismDobrushinField n) beta := by
  classical
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  have hfield : forall v : OddPrismLowerBlockSite n ⊕
      OddPrismUpperBlockSite n,
      Sum.elim
          (fun u : OddPrismLowerBlockSite n =>
            beta * oddPrismPlusField n u.1)
          (fun u : OddPrismUpperBlockSite n =>
            -(beta * oddPrismPlusField n u.1)) v =
        beta * oddPrismDobrushinField n (e v) := by
    intro v
    rcases v with v | v
    · have hv : ¬ n < v.1.z.val := by
        exact Nat.not_lt_of_ge v.2
      simp [e, oddPrismPlusField, oddPrismDobrushinField,
        oddRectangularPrismDobrushinSign, hv]
    · have hv : n < v.1.z.val := by
        simpa [oddPrismAtOrBelowCenter, Nat.not_le] using v.2
      simp [e, oddPrismPlusField, oddPrismDobrushinField,
        oddRectangularPrismDobrushinSign, hv]
  have h := ghsi_ZJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
    (fun v : OddPrismUpperBlockSite n =>
        -(beta * oddPrismPlusField n v.1)))
    (fun v => beta * oddPrismDobrushinField n v) hfield
  calc
    _ = ZJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismDobrushinField n v) := h
    _ = _ := by
      unfold scaledInhomogeneousPartition
      rw [oddPrismInternalGraph_edgeFinset]
      simp only [mul_one]


theorem rectangularPrismPlusPartition_eq_unequalBridge
    (beta : Real) (n : Nat) :
    rectangularPrismPlusPartition 1 beta (2 * n + 1) (2 * n + 1) n =
      ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        oddPrismUnequalBridgeMoment beta n beta := by
  classical
  rw [← scaledInhomogeneousPartition_oddPrismPlus,
    ← oddPrismUnequalGlue_plus_partition]
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  simpa [oddPrismUnequalBridgeMoment] using
    (ZJ_crossInterface_eq_mul_unequalMoment
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n)) beta
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))


theorem rectangularPrismDobrushinPartition_eq_unequalBridge
    (beta : Real) (n : Nat) :
    rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n =
      ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) *
        oddPrismUnequalBridgeMoment beta n (-beta) := by
  classical
  rw [← scaledInhomogeneousPartition_oddPrismDobrushin,
    ← oddPrismUnequalGlue_dobrushin_partition]
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  simpa [oddPrismUnequalBridgeMoment] using
    (ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n)) beta
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))


theorem rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge
    (beta : Real) (n : Nat) :
    StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta
        (2 * n + 1) (2 * n + 1) n =
      oddPrismUnequalBridgeFreeEnergy beta n := by
  classical
  let ZL := ZJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
  let ZU := ZJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
    (fun v => beta * oddPrismPlusField n v.1)
  have hbase : ZL * ZU ≠ 0 := mul_ne_zero
    (ZJ_pos _ _ _).ne' (ZJ_pos _ _ _).ne'
  have hplus := rectangularPrismPlusPartition_eq_unequalBridge beta n
  have hdobr := rectangularPrismDobrushinPartition_eq_unequalBridge beta n
  have hplusMoment : oddPrismUnequalBridgeMoment beta n beta ≠ 0 := by
    intro hm
    have hz : rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n = 0 := by
      simpa [ZL, ZU, hm] using hplus
    have hp : 0 < rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
      rw [← scaledInhomogeneousPartition_oddPrismPlus]
      unfold scaledInhomogeneousPartition
      exact ZJ_pos _ _ _
    exact hp.ne' hz
  have hdobrMoment : oddPrismUnequalBridgeMoment beta n (-beta) ≠ 0 := by
    intro hm
    have hz : rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n = 0 := by
      simpa [ZL, ZU, hm] using hdobr
    have hp : 0 < rectangularPrismDobrushinPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
      rw [← scaledInhomogeneousPartition_oddPrismDobrushin]
      unfold scaledInhomogeneousPartition
      exact ZJ_pos _ _ _
    exact hp.ne' hz
  rw [StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio,
    hplus, hdobr]
  change Real.log (ZL * ZU * oddPrismUnequalBridgeMoment beta n beta) -
      Real.log (ZL * ZU * oddPrismUnequalBridgeMoment beta n (-beta)) = _
  rw [Real.log_mul hbase hplusMoment,
    Real.log_mul hbase hdobrMoment]
  unfold oddPrismUnequalBridgeFreeEnergy
  ring


theorem standardCubicInterfaceDensity_eq_oddPrismUnequalBridge
    (beta : Real) (n : Nat) (hn : 0 < n) :
    standardCubicInterfaceDensity beta n =
      oddPrismUnequalBridgeFreeEnergy beta n /
        (((2 * n + 1 : Nat) : Real) ^ 2) := by
  rw [standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity
    beta n hn]
  unfold rectangularPrismInterfaceDensity
  rw [rectangularDobrushinFreeEnergy_eq_oddPrismUnequalBridge]


end
end StatMech.FrontierA
