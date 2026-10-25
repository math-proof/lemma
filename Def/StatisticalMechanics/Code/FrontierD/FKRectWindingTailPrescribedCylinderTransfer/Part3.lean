/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

def fkRectAfBottomIndex (R : FKRectTorus) (i : Nat) : Fin R.width :=
  ⟨(i + 1) % R.width, Nat.mod_lt _ R.width_pos⟩


def fkRectAfBottomIndexSet (R : FKRectTorus) (r : Nat) :
    Finset (Fin R.width) :=
  (Finset.range r).image (fkRectAfBottomIndex R)


end
end StatMech.FrontierD
