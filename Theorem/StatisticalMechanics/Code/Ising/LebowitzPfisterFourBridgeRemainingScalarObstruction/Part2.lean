/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleLowRank
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeRemainingScalarObstruction.Part2


namespace StatMech.Ising

noncomputable section

theorem fourBridgeSkewCounterexample_mem_establishedAggregateRegion :
    FourBridgeEstablishedAggregateRegion
      fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB
      fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
  norm_num [FourBridgeEstablishedAggregateRegion,
    fourBridgeSkewCounterexampleA, fourBridgeSkewCounterexampleB,
    fourBridgeSkewCounterexampleC, fourBridgeSkewCounterexampleD,
    fourBridgeRankMass]


theorem fourBridgeSkewCounterexample_polynomial_pos :
    0 < fourBridgeVarianceSkewPolynomial
      (9 / 10) fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB
      fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
  norm_num [fourBridgeVarianceSkewPolynomial,
    fourBridgeSkewCounterexampleA, fourBridgeSkewCounterexampleB,
    fourBridgeSkewCounterexampleC, fourBridgeSkewCounterexampleD]

end
end StatMech.Ising
