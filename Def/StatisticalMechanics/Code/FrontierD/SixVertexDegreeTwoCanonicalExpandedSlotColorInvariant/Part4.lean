/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
    mask false layer dart
  let arrival := alignedBoundaryPerm homega heta hdegree false input
  let common := if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm arrival
    else arrival
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask true
    layer common

end
end StatMech.FrontierD
