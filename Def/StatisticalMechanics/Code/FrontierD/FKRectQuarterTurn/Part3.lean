/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part2
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnVertexEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) :
    R.Vertex ≃ (fkRectQuarterTurnTorus R hheight).Vertex where
  toFun := fkRectQuarterTurnVertex R hheight
  invFun := fkRectQuarterTurnVertexInv R hheight
  left_inv := fkRectQuarterTurnVertexInv_left R hheight
  right_inv := fkRectQuarterTurnVertexInv_right R hheight

end
end StatMech.FrontierD
