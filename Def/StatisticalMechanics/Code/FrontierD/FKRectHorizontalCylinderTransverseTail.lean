module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseDiagonalBound
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailLaw
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseTail


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseTail.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectWindingTailForcesHorizontalCylinderCrossings
    (R : FKRectTorus) (r : Nat) : Prop :=
  forall omega, r <= fkRectUnorientedVerticalWindingNumber R omega ->
    r <= fkRectHorizontalCutPrimalCrossingClusterCount R
      (fkRectForceHorizontalCutClosed R omega)


end
end StatMech.FrontierD
