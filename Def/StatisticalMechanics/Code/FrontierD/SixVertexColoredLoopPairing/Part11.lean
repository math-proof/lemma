/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part13


namespace StatMech.FrontierD

noncomputable section

def FKColoredVertexCrossBondCoherent
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredVertexCrossRawColor source mask (fkLayeredBondMate T x) =
      fkColoredVertexCrossRawColor source mask x


def fkColoredVertexCrossTarget
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    FKColoredLoopPairingPair T := fun layer =>
  { pairing := (source layer).pairing
    color := fun d => fkColoredVertexCrossRawColor source mask (layer, d)
    color_localMate := fkColoredVertexCrossRawColor_localMate source mask layer
    color_bondMate := by
      intro d
      exact hbond (layer, d) }

end
end StatMech.FrontierD
