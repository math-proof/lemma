/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseDiagonalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailLaw
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseTail


namespace StatMech.FrontierD

noncomputable section

def FKRectWindingTailForcesHorizontalCylinderCrossings
    (R : FKRectTorus) (r : Nat) : Prop :=
  forall omega, r <= fkRectUnorientedVerticalWindingNumber R omega ->
    r <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R omega)


end
end StatMech.FrontierD
