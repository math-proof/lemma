module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part3
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech

noncomputable section

def fkRectAfPair (R : FKRectTorus) : Fin R.width → Fin R.width :=
  id


def FKRectAfWindingTailPrescribedCylinderRepair
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex) : Prop :=
  (fkRectAfBottomIndexSet R r).card = r ∧
    FKRectWindingTailPrescribedCylinderRepair R r I
      (fkRectAfPair R) (fkRectAfBottomIndexSet R r)

end
end StatMech.FrontierD
