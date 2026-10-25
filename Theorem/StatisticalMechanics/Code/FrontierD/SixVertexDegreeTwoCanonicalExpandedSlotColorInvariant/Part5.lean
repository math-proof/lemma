/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedRecoverPairing_eq_source
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoCanonicalExpandedRecoverPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · simp [sixVertexDegreeTwoCanonicalExpandedRecoverPairing, cut, hleft,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover,
      sixVertexDegreeTwoAlignedTargetPairing_of_left_empty]
  · by_cases hright : cut.cutRight = []
    · simp [sixVertexDegreeTwoCanonicalExpandedRecoverPairing, cut, hleft,
        hright, sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover,
        sixVertexDegreeTwoAlignedTargetPairing_of_right_empty]
    · rw [sixVertexDegreeTwoCanonicalExpandedRecoverPairing]
      simp only [cut, hleft, hright, dite_false]
      rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover]
      exact sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper homega
        heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

end
end StatMech.FrontierD
