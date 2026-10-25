/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part5


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoAlignedColoredSource
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    FKColoredLoopPairingPair T
  | false =>
      SixVertexCompatibleLoopPairing.toColored
        ⟨alignedRoutingLoopPairing homega heta hdegree false,
          alignedRoutingPairing_compatible homega heta hdegree false⟩
  | true =>
      SixVertexCompatibleLoopPairing.toColored
        ⟨alignedRoutingLoopPairing homega heta hdegree true,
          alignedRoutingPairing_compatible homega heta hdegree true⟩

end
end StatMech.FrontierD
