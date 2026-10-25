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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

def FKRectWindingTailPrescribedCylinderRepair
    (R : FKRectTorus) (r : Nat) (I : Finset R.EdgeIndex)
    (pair : Fin R.width → Fin R.width) (S : Finset (Fin R.width)) : Prop :=
  ∀ omega, r ≤ fkRectUnorientedVerticalWindingNumber R omega →
    ∃ eta : FKRectLocalPattern R I,
      let tau := fkRectForceLocalPattern R I eta omega
      FKRectHorizontalCutClosedConfiguration R tau ∧
        FKRectHorizontalCylinderStablePairedWitnessCore R pair S tau


end
end StatMech.FrontierD
