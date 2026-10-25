/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part9


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta
        hdegree middle homegaSector hetaSector hmiddle layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta
    hdegree middle homegaSector hetaSector hmiddle layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive homega heta
      hdegree middle homegaSector hetaSector hmiddle layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive homega heta
      hdegree middle homegaSector hetaSector hmiddle layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta
          hdegree middle homegaSector hetaSector hmiddle layer dart) := by
  rw [sixVertexDegreeTwoBranchClosedExpandedTargetBoundary]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl


end
end StatMech.FrontierD
