/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample.Part3
open Finset


namespace StatMech.Ising

noncomputable section

theorem fourBridgePointwiseCutCounterexample_fourierRecovery :
    let p0 : Real := 0
    let p1 : Real := 1 / 3
    let p2 : Real := 1 / 3
    let p3 : Real := 0
    let p4 : Real := 1 / 3
    fourBridgePointwiseCutCounterexampleA = 4 * (p4 - p0) + 2 * (p3 - p1) ∧
      fourBridgePointwiseCutCounterexampleB = 6 * (p0 + p4) - 2 * p2 ∧
      fourBridgePointwiseCutCounterexampleC = 4 * (p4 - p0) + 2 * (p1 - p3) ∧
      fourBridgePointwiseCutCounterexampleD = p0 - p1 + p2 - p3 + p4 := by
  norm_num [fourBridgePointwiseCutCounterexampleA,
    fourBridgePointwiseCutCounterexampleB,
    fourBridgePointwiseCutCounterexampleC,
    fourBridgePointwiseCutCounterexampleD]


theorem fourBridgePointwiseCutCounterexample_numerator_eq :
    fourBridgeSecondMiddleNumerator
      fourBridgePointwiseCutCounterexampleA
      fourBridgePointwiseCutCounterexampleB
      fourBridgePointwiseCutCounterexampleC
      fourBridgePointwiseCutCounterexampleD = -(64 / 9) := by
  norm_num [fourBridgeSecondMiddleNumerator,
    fourBridgePointwiseCutCounterexampleA,
    fourBridgePointwiseCutCounterexampleB,
    fourBridgePointwiseCutCounterexampleC,
    fourBridgePointwiseCutCounterexampleD]

theorem fourBridgePointwiseCutCounterexample_numerator_neg :
    fourBridgeSecondMiddleNumerator
      fourBridgePointwiseCutCounterexampleA
      fourBridgePointwiseCutCounterexampleB
      fourBridgePointwiseCutCounterexampleC
      fourBridgePointwiseCutCounterexampleD < 0 := by
  rw [fourBridgePointwiseCutCounterexample_numerator_eq]
  norm_num


theorem fourBridgePointwiseCutCounterexample_not_strictlyPositive :
    fourBridgePointwiseCutCounterexampleMass (∅ : Finset (Fin 4)) = 0 := by
  norm_num [fourBridgePointwiseCutCounterexampleMass,
    fourBridgePointwiseCutCounterexampleWeight]

end
end StatMech.Ising
