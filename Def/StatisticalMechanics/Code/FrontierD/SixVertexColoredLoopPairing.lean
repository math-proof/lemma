/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part2


namespace StatMech.FrontierD

noncomputable section

def FKColoredLoopPairing.incoming
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) : Bool :=
  fkMedialCheckerColor d ^^ colored.color d

def FKColoredLoopPairing.arrows
    {T : EvenTorus} (colored : FKColoredLoopPairing T) : SixVertexArrows T where
  horizontal v := !colored.incoming (v, .east)
  vertical v := !colored.incoming (v, .north)

end
end StatMech.FrontierD
