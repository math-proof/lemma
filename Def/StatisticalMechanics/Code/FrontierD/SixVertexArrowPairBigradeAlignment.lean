/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowStrandSlotColor
    {T : EvenTorus} (omega : SixVertexArrows T)
    (slot : T.Vertex × Bool) : Bool :=
  sixVertexArrowPairStrandSlotColor omega omega
    (false, slot.1, slot.2)

def sixVertexArrowCheckerHorizontalAgreementCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {v : T.Vertex //
    omega.horizontal v = fkMedialVertexParity v}

end
end StatMech.FrontierD
