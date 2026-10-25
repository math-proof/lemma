/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part8
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem oddPrismUnequalBridgeVarianceOrder_iff_crossField
    (beta : Real) (n : Nat) :
    OddPrismUnequalBridgeVarianceOrder beta n <->
      OddPrismUnequalBridgeCrossFieldVarianceOrder beta n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold OddPrismUnequalBridgeVarianceOrder
    OddPrismUnequalBridgeCrossFieldVarianceOrder
  constructor <;> intro h t ht
  · rw [← unequalReplicaBridgeVariance_neg_eq_negRightField
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n))]
    exact h t ht
  · rw [unequalReplicaBridgeVariance_neg_eq_negRightField
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n)
      (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph n)
        (oddPrismAtOrBelowCenter n))]
    exact h t ht


theorem oddPrismUnequalBridgeFreeEnergy_le_of_variance_order
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (hvar : OddPrismUnequalBridgeVarianceOrder beta n) :
    oddPrismUnequalBridgeFreeEnergy beta n <=
      2 * beta * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  change unequalReplicaBridgeFreeEnergy
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta
      (fun v => beta * oddPrismPlusField n v.1)
      (fun v => beta * oddPrismPlusField n v.1) beta <= _
  apply unequalReplicaBridgeFreeEnergy_le_of_variance_order
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) beta hbeta
  exact hvar

end
end StatMech.FrontierA
