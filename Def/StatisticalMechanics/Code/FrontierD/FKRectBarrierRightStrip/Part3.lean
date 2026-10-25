/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectLeftBarrierWithSeamPattern (R : FKRectTorus)
    (leftRight : Nat) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Set R.Configuration :=
  fkRectNoLeftStripCrossingEvent R leftRight ∩
    fkRectIndexedPatternEvent R I eta

end
end StatMech.FrontierD
