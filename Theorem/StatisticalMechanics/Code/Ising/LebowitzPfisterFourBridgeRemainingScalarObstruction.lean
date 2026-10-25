/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleLowRank
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeRemainingScalarObstruction


namespace StatMech.Ising

noncomputable section

theorem fourBridgeRemainingCounterexample_mem_establishedAggregateRegion :
    FourBridgeEstablishedAggregateRegion
      fourBridgeRemainingCounterexampleA
      fourBridgeRemainingCounterexampleB
      fourBridgeRemainingCounterexampleC
      fourBridgeRemainingCounterexampleD := by
  norm_num [FourBridgeEstablishedAggregateRegion,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD,
    fourBridgeRankMass]


theorem fourBridgeRemainingCounterexample_closed_coefficients_nonpos :
    fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 0 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 1 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 2 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 5 <= 0 ∧
      fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 6 <= 0 := by
  norm_num [fourBridgeVarianceSkewBernsteinCoeff,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD]


theorem fourBridgeRemainingCounterexample_middle_three_four_pos :
    0 < fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 3 ∧
      0 < fourBridgeVarianceSkewBernsteinCoeff
        fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB
        fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 4 := by
  norm_num [fourBridgeVarianceSkewBernsteinCoeff,
    fourBridgeRemainingCounterexampleA, fourBridgeRemainingCounterexampleB,
    fourBridgeRemainingCounterexampleC, fourBridgeRemainingCounterexampleD]

end
end StatMech.Ising
