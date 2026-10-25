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
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexDoubledBalancedShare (N M : Nat) (c : Real) : Real :=
  sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c /
    sixVertexRectangleToroidalPartitionSum (N + N) (M + M) c


end
end StatMech.FrontierD
