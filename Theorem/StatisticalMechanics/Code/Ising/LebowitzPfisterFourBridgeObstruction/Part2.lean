/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction.Part2


namespace StatMech.Ising

noncomputable section

theorem fourBridgeVarianceSkewBernsteinCoeff_zero_eq_thirdCumulant
    (a b c d : Real) :
    2 * fourBridgeVarianceSkewBernsteinCoeff a b c d 0 =
      (10 * a + 6 * c) - 3 * (4 + 2 * b) * a + 2 * a ^ 3 := by
  unfold fourBridgeVarianceSkewBernsteinCoeff
  ring


end
end StatMech.Ising
