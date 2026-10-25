/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectDualPullbackIndexSet (R : FKRectTorus)
    (I : Finset R.EdgeIndex) : Finset R.EdgeIndex :=
  I.image (fkRectDualEdgeToEdge R)


def fkRectDualPullbackConfiguration (R : FKRectTorus)
    (eta : R.Configuration) : R.Configuration :=
  fun e => !(eta (fkRectEdgeToDualEdge R e))

end
end StatMech.FrontierD
