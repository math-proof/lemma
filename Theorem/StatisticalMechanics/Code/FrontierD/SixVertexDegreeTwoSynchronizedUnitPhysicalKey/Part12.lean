/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part11


namespace StatMech.FrontierD

noncomputable section

theorem
    sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
    (hnext : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta
        hdegree component layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]


theorem
    sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta
          hdegree component layer dart) := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl


theorem
    sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component)
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component))
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component)
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
        heta hdegree component) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree
    layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  change fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
        hdegree component
        (fkColoredLayeredStrandSlotBoundaryPerm
          (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
            heta hdegree component) (layer, slot))) = _
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart


theorem sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) →
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component)
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component))
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component)
      (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
        heta hdegree component) := by
  apply sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart
    homega heta hdegree component
  intro layer dart
  by_cases hdart : activeBlackDart (omega := omega) (eta := eta) dart
  · exact hactive layer dart (Or.inl hdart)
  · by_cases hnext : activeBlackDart (omega := omega) (eta := eta)
        (alignedBoundaryPerm homega heta hdegree false dart)
    · exact hactive layer dart (Or.inr hnext)
    · rw [sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive
        homega heta hdegree component layer dart hdart hnext]
      exact
        sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive
          homega heta hdegree component layer dart hnext


end
end StatMech.FrontierD
