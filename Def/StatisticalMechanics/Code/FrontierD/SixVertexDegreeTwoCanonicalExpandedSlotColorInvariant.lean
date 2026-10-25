/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalTransitionMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex) : Bool := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · exact false
  · by_cases hright : cut.cutRight = []
    · exact false
    · exact decide (v = doubledAlignedVertex (cut.cutRight.head hright)) ||
        decide (v = doubledAlignedVertex (cut.cutLeft.head hleft))

end
end StatMech.FrontierD
