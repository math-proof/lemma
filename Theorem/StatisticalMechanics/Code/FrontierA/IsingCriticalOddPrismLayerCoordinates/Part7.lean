/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part7


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismGraphBridgeRawMoment_pos
    (beta : Real) (n : Nat) (r : Real) :
    0 < oddPrismGraphBridgeRawMoment beta n r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment
  apply Finset.sum_pos
  · intro a _
    apply Finset.sum_pos
    · intro b _
      exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
        (Real.exp_pos _)
    · exact Finset.univ_nonempty
  · exact Finset.univ_nonempty


theorem oddPrismUnequalBridgeVariance_eq_graphRaw
    (beta : Real) (n : Nat) (r : Real) :
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) r =
      oddPrismGraphBridgeRawSecond beta n r /
          oddPrismGraphBridgeRawMoment beta n r -
        (oddPrismGraphBridgeRawFirst beta n r /
          oddPrismGraphBridgeRawMoment beta n r) ^ 2 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold unequalReplicaBridgeVariance unequalReplicaBridgeMean
    unequalReplicaBridgeMoment oddPrismGraphBridgeRawMoment
    oddPrismGraphBridgeRawFirst oddPrismGraphBridgeRawSecond
  have hmul (a : ConfigSpace (OddPrismLowerBlockSite n))
      (b : ConfigSpace (OddPrismUpperBlockSite n)) :
      unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b * r =
        r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b := by ring
  field_simp [
    (ZJ_pos (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne',
    (ZJ_pos (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne']
  simp_rw [hmul]
  ring


theorem oddPrismGraphBridgeRawMoment_beta_eq_plusPartition
    (beta : Real) (n : Nat) :
    oddPrismGraphBridgeRawMoment beta n beta =
      rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  rw [rectangularPrismPlusPartition_eq_unequalBridge]
  unfold oddPrismUnequalBridgeMoment unequalReplicaBridgeMoment
    oddPrismGraphBridgeRawMoment
  field_simp [
    (ZJ_pos (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne',
    (ZJ_pos (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
      (fun v => beta * oddPrismPlusField n v.1)).ne']


theorem oddPrismTransferBridgeRawMoment_beta_eq_plusPartition
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismTransferBridgeRawMoment beta n beta =
      rectangularPrismPlusPartition 1 beta
        (2 * n + 1) (2 * n + 1) n := by
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction,
    oddPrismTiltedSeamTransfer_eq_rectangularTransfer]
  rw [← oddPrismLowerTransferTail_eq_mulVec_upper beta n hn]
  rw [rectangularPrismPlusPartition_eq_centerDenominator]
  apply Finset.sum_congr rfl
  intro s _
  simp only [oddPrismLowerTransferTail, pow_two]


theorem oddPrismGraphBridgeRawMoment_beta_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) :
    oddPrismGraphBridgeRawMoment beta n beta =
      oddPrismTransferBridgeRawMoment beta n beta := by
  rw [oddPrismGraphBridgeRawMoment_beta_eq_plusPartition,
    oddPrismTransferBridgeRawMoment_beta_eq_plusPartition beta n hn]


end
end StatMech.FrontierA
