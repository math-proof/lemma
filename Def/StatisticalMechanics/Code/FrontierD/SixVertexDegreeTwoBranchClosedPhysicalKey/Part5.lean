/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part5


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoBranchClosedSelectedStateFinIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    Fin (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle)) :=
  Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    ⟨doubledAlignedBlackDart homega heta hdegree false x,
      (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mpr hx⟩

end
end StatMech.FrontierD
