/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoAlignedSelectedStateFinIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    Fin (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle)) :=
  Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    ⟨doubledAlignedBlackDart homega heta hdegree false x,
      (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mpr hx⟩

end
end StatMech.FrontierD
