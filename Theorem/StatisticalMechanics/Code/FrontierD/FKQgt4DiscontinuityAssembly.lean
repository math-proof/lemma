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
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkQgt4CriticalFreeDiagonalTwoPoint_nonneg
    {q : Real} (hq : 4 < q) (n : Nat) :
    0 <= fkQgt4CriticalFreeDiagonalTwoPoint hq n :=
  measureReal_nonneg

theorem fkQgt4CriticalFreeDiagonalTwoPoint_le_one
    {q : Real} (hq : 4 < q) (n : Nat) :
    fkQgt4CriticalFreeDiagonalTwoPoint hq n <= 1 :=
  measureReal_le_one


end
end StatMech.FrontierD
