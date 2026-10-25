/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part8


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) :=
  (sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective homega heta
    hdegree middle homegaSector hetaSector hmiddle layer).comp
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm.injective


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer i =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer) dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
          homegaSector hetaSector hmiddle)).symm i
    have hdart : occurrence.1 = dart := by
      apply (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer)).injective
      exact hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
        homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
      sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)


theorem sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree layer) dart) =
      (!layer, fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree (!layer)) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
      hdegree middle homegaSector hetaSector hmiddle := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
      homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle currentLayer i =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree currentLayer) dart := by
    unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
      sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]


theorem sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree layer) dart) =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer) dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree false dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
            middle homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, fkColoredBlackDartStrandSlotEquiv
            (alignedRoutingLoopPairing homega heta hdegree true) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree false dart) := by
  classical
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle false dart
        hdart]
    rfl
  · rw [dif_neg hdart,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle false dart
        hdart]


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_trueDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (dart : FKMedialBlackDart T) :
    let physical := alignedBlackDartLayerSwap homega heta hdegree dart
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree true dart)) =
      if _hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
          hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, fkColoredBlackDartStrandSlotEquiv
            (alignedRoutingLoopPairing homega heta hdegree false) physical)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree true dart) := by
  classical
  let physical := alignedBlackDartLayerSwap homega heta hdegree dart
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
  change fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) physical)) =
    if _hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
        hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) physical)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) physical)
  by_cases hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
      hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hphysical,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle true
        physical hphysical]
    rfl
  · rw [dif_neg hphysical,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle true
        physical hphysical]


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
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
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  have hslot (currentLayer : Bool) :
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree currentLayer) dart := by
    cases currentLayer
    · exact sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false homega heta
        hdegree dart
    · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
        alignedBlackDartLayerSwap_inactive homega heta hdegree dart hinactive]
  rw [hslot layer]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
    have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    rw [hslot false, hslot true] at hcross
    cases layer
    · exact hcross.symm
    · exact hcross
  · rw [
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
        hdart]


theorem sixVertexDegreeTwoCanonicalPhysicalExpanded_falseDart_color_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
              hdegree middle homegaSector hetaSector hmiddle layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  have hmask := sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega
    heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart
  rw [sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked homega
      heta hdegree middle homegaSector hetaSector hmiddle layer dart hmask
      hnext,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      (alignedBoundaryPerm homega heta hdegree false dart) hnext,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
  exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    homega heta hdegree layer dart hnext


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState
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
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) := by
  unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
    sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (doubledAlignedBlackDart homega heta hdegree false x) = _
  rw [← sixVertexDegreeTwoTauAdjustedState_trueDart
    homega heta hdegree x]
  exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _

theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false
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
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree false x) := by
  unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
    sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _

end
end StatMech.FrontierD
