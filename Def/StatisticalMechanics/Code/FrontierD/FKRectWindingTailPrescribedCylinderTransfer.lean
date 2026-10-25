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
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

def fkRectLocalPatternExtension (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I) :
    R.Configuration := fun a => if ha : a ∈ I then eta ⟨a, ha⟩ else false


def fkRectForceLocalPattern (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : FKRectLocalPattern R I)
    (omega : R.Configuration) : R.Configuration :=
  fkRectForceIndexedPattern R I (fkRectLocalPatternExtension R I eta) omega

end
end StatMech.FrontierD
