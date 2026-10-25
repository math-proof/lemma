/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexRetieAtTransitionVertices
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) : FKMedialLoopPairing T :=
  if first = second then fkMedialTogglePairingAt pairing first
  else fkMedialTogglePairingAt
    (fkMedialTogglePairingAt pairing first) second


noncomputable def sixVertexDegreeTwoAlignedTargetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) : FKMedialLoopPairing T := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · exact alignedRoutingLoopPairing homega heta hdegree layer
  · by_cases hright : cut.cutRight = []
    · exact alignedRoutingLoopPairing homega heta hdegree layer
    · exact sixVertexRetieAtTransitionVertices
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (doubledAlignedVertex (cut.cutRight.head hright))
        (doubledAlignedVertex (cut.cutLeft.head hleft))

end
end StatMech.FrontierD
