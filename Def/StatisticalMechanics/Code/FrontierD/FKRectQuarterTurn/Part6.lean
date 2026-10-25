/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part5
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnEdgeEquiv (R : FKRectTorus)
    (hheight : 4 < R.height) :
    R.EdgeIndex ≃ (fkRectQuarterTurnTorus R hheight).EdgeIndex where
  toFun := fkRectQuarterTurnEdge R hheight
  invFun := fkRectQuarterTurnEdgeInv R hheight
  left_inv := fkRectQuarterTurnEdgeInv_left R hheight
  right_inv := fkRectQuarterTurnEdgeInv_right R hheight

end
end StatMech.FrontierD
