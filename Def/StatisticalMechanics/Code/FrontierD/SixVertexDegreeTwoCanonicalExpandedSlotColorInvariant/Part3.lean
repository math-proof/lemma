/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part2


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalExpandedRetieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v

end
end StatMech.FrontierD
