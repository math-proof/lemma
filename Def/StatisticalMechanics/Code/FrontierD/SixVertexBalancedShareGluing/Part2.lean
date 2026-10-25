/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareGluing
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectFourCopyShareCost (R : FKRectTorus) (q : Real) : Real :=
  Real.log (sixVertexRectangleToroidalPartitionSum
      (R.width + R.width) (R.height / 2 + R.height / 2)
      (fkQgt4SixVertexWeight q)) -
    4 * Real.log (sixVertexRectangleToroidalPartitionSum
      R.width (R.height / 2) (fkQgt4SixVertexWeight q)) +
    (4 * (R.width + R.height / 2) : Nat) * Real.log 2

end
end StatMech.FrontierD
