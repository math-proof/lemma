/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalExpandedTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) =
      (fkColoredParityMaskStrandSlotSwap
        (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
        (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer) true)) := by
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask]
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _


end
end StatMech.FrontierD
