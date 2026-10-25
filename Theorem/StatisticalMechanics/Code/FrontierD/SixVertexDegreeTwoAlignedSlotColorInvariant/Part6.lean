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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosedExpandedTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer) =
      (fkColoredParityMaskStrandSlotSwap
        (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
        (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _

@[simp] theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _

@[simp] theorem sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v = false := by
  have hnot : Not ((sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
  simp [sixVertexDegreeTwoBranchClosedExpandedRetieMask,
    sixVertexDegreeTwoBranchClosedTransitionVertex,
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex, hnot]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [sixVertexDegreeTwoBranchClosedExpandedTargetPairing,
    fkMedialTogglePairingMask,
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer v hzero]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let transition := sixVertexDegreeTwoBranchClosedTransitionVertex
      homega heta hdegree middle homegaSector hetaSector hmiddle v
    let internal := sixVertexDegreeTwoBranchClosedInternalMismatchVertex
      homega heta hdegree middle homegaSector hetaSector hmiddle v
    sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer v =
      if transition || internal then
        !(if layer then
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ
        else (orientedDartAlignedRetie homega heta hdegree d).pairingP)
      else if layer then
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hsource := alignedRoutingPairing_eq_at_active
    homega heta hdegree layer v hactive
  change alignedRoutingLoopPairing homega heta hdegree layer v =
    (if layer then (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP) at hsource
  rw [sixVertexDegreeTwoBranchClosedExpandedTargetPairing,
    fkMedialTogglePairingMask, hsource]
  rfl

theorem sixVertexDegreeTwoBranchClosedTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments
          homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments
      homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]
  · rw [dif_neg hdart,
      sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
        (doubledAlignedBlackDart homega heta hdegree false x) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) := by
  cases layer
  · exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree false) _
  · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
      alignedBlackDartLayerSwap_active]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree true) _


theorem sixVertexDegreeTwoBranchClosedTransportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta
          hdegree middle homegaSector hetaSector hmiddle then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle) x
  by_cases hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta
      hdegree middle homegaSector hetaSector hmiddle
  · rw [dif_pos (hmem.mpr hx), dif_pos hx]
    simp
  · rw [dif_neg (fun hdart => hx (hmem.mp hdart)), dif_neg hx]

theorem sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoBranchClosedTransportedColor_dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl


theorem sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (if layer then
          (alignedBlackDartLayerSwap homega heta hdegree).symm
            (alignedBoundaryPerm homega heta hdegree false dart)
        else alignedBoundaryPerm homega heta hdegree false dart) := by
  cases layer
  · simp only [Bool.false_eq_true, if_false,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
    change (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false))
          ((alignedBoundaryPerm homega heta hdegree false)
            ((fkColoredBlackDartStrandSlotEquiv
              (alignedRoutingLoopPairing homega heta hdegree false)).symm
              ((fkColoredBlackDartStrandSlotEquiv
                (alignedRoutingLoopPairing homega heta hdegree false)) dart))) =
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false))
          ((alignedBoundaryPerm homega heta hdegree false) dart)
    rw [Equiv.symm_apply_apply]
  · let swap := alignedBlackDartLayerSwap homega heta hdegree
    let next := alignedBoundaryPerm homega heta hdegree false dart
    have hstep : alignedBoundaryPerm homega heta hdegree true (swap dart) =
        next := (alignedBoundaryPerm_false_eq_true_layerSwap
          homega heta hdegree dart).symm
    simp only [if_true,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
    change fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap dart)) =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (swap (swap.symm next))
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact congrArg
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)) hstep


end
end StatMech.FrontierD
