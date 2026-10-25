/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part8


namespace StatMech.FrontierD

noncomputable section

def FKColoredLoopPairing.localPairing
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex) :
    FKColoredLocalPairing where
  pairing := colored.pairing v
  west := colored.color (v, .west)
  east := colored.color (v, .east)

end
end StatMech.FrontierD
