/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part5
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveBandBlockAssembledEvent
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    Set R.Configuration :=
  ((fkRectEvenRowBlockIntersection R B.carrier B.start B.finish
      B.step (fkRectPositiveBandBulkBlocks B) ∩
    fkRectPositiveBandBlockBottomConnectorEvent B hheight) ∩
    fkRectPositiveBandBlockTopConnectorEvent B hheight) ∩
    fkRectUnitAttachmentOpenEvent R

end
end StatMech.FrontierD
