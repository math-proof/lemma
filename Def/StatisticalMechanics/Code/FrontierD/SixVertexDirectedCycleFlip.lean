/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip


namespace StatMech.FrontierD

noncomputable section

def sixVertexLocalFlipMask
    (pattern mask : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern :=
  fun side => if mask side then !pattern side else pattern side


def sixVertexLocalSelectedIncomingCount
    (pattern mask : SixVertexLocalIncomingPattern) : Nat :=
  ∑ side, if mask side then (pattern side).toNat else 0


end
end StatMech.FrontierD
