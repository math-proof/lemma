/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part4


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) (layer : Bool) :
    sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) := by
  unfold sixVertexDegreeTwoAlignedBoundaryFinKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  cases layer
  · change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedBlackDart homega heta hdegree false x) = _
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree false) _
  · change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (alignedBlackDartLayerSwap homega heta hdegree
        (doubledAlignedBlackDart homega heta hdegree false x)) = _
    rw [alignedBlackDartLayerSwap_active]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree true) _


end
end StatMech.FrontierD
