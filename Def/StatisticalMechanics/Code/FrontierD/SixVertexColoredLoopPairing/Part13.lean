/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part15


namespace StatMech.FrontierD

noncomputable section

def fkColoredVertexCrossSeamDelta
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (layer : Bool) : Int :=
  ∑ i : Fin T.width, (
    ((fkColoredVertexCrossTarget source mask hbond layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat -
      ((source layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat : Int)

end
end StatMech.FrontierD
