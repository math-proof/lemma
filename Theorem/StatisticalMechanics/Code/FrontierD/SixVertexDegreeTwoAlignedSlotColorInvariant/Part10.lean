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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (slot : T.Vertex × Bool) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (sixVertexDegreeTwoAlignedFalseDartOfSlot
          homega heta hdegree layer slot) = slot := by
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).apply_symm_apply
        slot
  · simp [sixVertexDegreeTwoAlignedFalseDartOfSlot,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart]


theorem sixVertexDegreeTwoBranchClosedSlotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hfalseDart : forall (layer : Bool) (dart : FKMedialBlackDart T),
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
              homega heta hdegree layer
              (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart
                homega heta hdegree middle homegaSector hetaSector hmiddle
                layer dart))) =
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
              homega heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta
        hdegree middle homegaSector hetaSector hmiddle) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot
    homega heta hdegree layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  rw [← hslot,
    fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart

theorem fkColoredVertexStrandSlotSwap_apply_of_fst_ne
    {T : EvenTorus} (v : T.Vertex) (slot : T.Vertex × Bool)
    (hne : slot.1 ≠ v) :
    fkColoredVertexStrandSlotSwap v slot = slot := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hne (congrArg Prod.fst h)
  · intro h
    exact hne (congrArg Prod.fst h)


theorem fkColoredStrandSlotBoundaryPerm_retie_apply_of_away
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) (slot : T.Vertex × Bool)
    (hfirst : if fkMedialVertexParity first = true then
        (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ first
      else slot.1 ≠ first)
    (hsecond : if fkMedialVertexParity second = true then
        (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ second
      else slot.1 ≠ second) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) slot =
      fkColoredStrandSlotBoundaryPerm pairing slot := by
  by_cases hvertices : first = second
  · rw [fkColoredStrandSlotBoundaryPerm_retie_of_eq
      pairing hvertices]
    by_cases hp : fkMedialVertexParity first = true
    · rw [if_pos hp]
      simp only [Equiv.trans_apply]
      exact fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
        (by simpa [hp] using hfirst)
    · rw [if_neg hp]
      simp only [Equiv.trans_apply]
      rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
        (by simpa [hp] using hfirst)]
  · have hvertices' : first != second := bne_iff_ne.mpr hvertices
    rw [fkColoredStrandSlotBoundaryPerm_retie_of_ne
      pairing hvertices']
    by_cases hpSecond : fkMedialVertexParity second = true
    · rw [if_pos hpSecond]
      by_cases hpFirst : fkMedialVertexParity first = true
      · rw [if_pos hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
            (by simpa [hpFirst] using hfirst),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne second _
            (by simpa [hpSecond] using hsecond)]
      · rw [if_neg hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
            (by simpa [hpFirst] using hfirst),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne second _
            (by simpa [hpSecond] using hsecond)]
    · rw [if_neg hpSecond]
      by_cases hpFirst : fkMedialVertexParity first = true
      · rw [if_pos hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne second slot
            (by simpa [hpSecond] using hsecond),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
            (by simpa [hpFirst] using hfirst)]
      · rw [if_neg hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne second slot
            (by simpa [hpSecond] using hsecond),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
            (by simpa [hpFirst] using hfirst)]


theorem sixVertexDegreeTwoAlignedTargetBoundary_apply_of_away
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) (slot : T.Vertex × Bool)
    (hrightAway :
      let rightVertex := doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright)
      if fkMedialVertexParity rightVertex = true then
        (fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠
            rightVertex
      else slot.1 ≠ rightVertex)
    (hleftAway :
      let leftVertex := doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)
      if fkMedialVertexParity leftVertex = true then
        (fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠
            leftVertex
      else slot.1 ≠ leftVertex) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
          homegaSector hetaSector hmiddle layer) slot =
      fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree layer) slot := by
  rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper
    homega heta hdegree middle homegaSector hetaSector hmiddle
    hleft hright layer]
  exact fkColoredStrandSlotBoundaryPerm_retie_apply_of_away _ _ _ _
    hrightAway hleftAway


theorem sixVertexDegreeTwoAlignedTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments
          homega heta hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
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
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]
  · rw [dif_neg hdart,
      sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]


theorem sixVertexDegreeTwoAlignedTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoAlignedTransportedColor_dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl


theorem sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer
          (alignedBoundaryPerm homega heta hdegree false dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  let source := sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
  cases layer
  · have hboundary := FKColoredLoopPairing.slotColor_boundaryPerm
      source false
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false) dart)
    have hpairing : (source false).pairing =
        alignedRoutingLoopPairing homega heta hdegree false := rfl
    rw [hpairing] at hboundary
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply] at hboundary
    change fkColoredLayeredSlotColor source
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
          (alignedBoundaryPerm homega heta hdegree false dart)) =
      fkColoredLayeredSlotColor source
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) dart)
    exact hboundary
  · let swap := alignedBlackDartLayerSwap homega heta hdegree
    let next := alignedBoundaryPerm homega heta hdegree false dart
    have hnext : alignedBoundaryPerm homega heta hdegree true (swap dart) =
        next := by
      exact (alignedBoundaryPerm_false_eq_true_layerSwap
        homega heta hdegree dart).symm
    have hswapNext : swap next = next :=
      alignedBlackDartLayerSwap_inactive
        homega heta hdegree next hinactive
    have hboundary := FKColoredLoopPairing.slotColor_boundaryPerm
      source true
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true) (swap dart))
    have hpairing : (source true).pairing =
        alignedRoutingLoopPairing homega heta hdegree true := rfl
    rw [hpairing] at hboundary
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply] at hboundary
    change fkColoredLayeredSlotColor source
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap next)) =
      fkColoredLayeredSlotColor source
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap dart))
    rw [hswapNext]
    have hnext' : fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true) (swap dart) =
        next := hnext
    rw [hnext'] at hboundary
    exact hboundary


theorem sixVertexDegreeTwoBranchClosedExpanded_falseDart_color_of_inactive
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
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega
              heta hdegree middle homegaSector hetaSector hmiddle layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  rw [sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart hnext,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      (alignedBoundaryPerm homega heta hdegree false dart) hnext,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
  exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    homega heta hdegree layer dart hnext


theorem sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) := by
  classical
  let selected := SixVertexDegreeTwoAlignedSelectedStates
    homega heta hdegree middle homegaSector hetaSector hmiddle
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false selected dart hinactive
  rw [sixVertexDegreeTwoAlignedTransportedColor_dart,
    sixVertexDegreeTwoAlignedTransportedColor_dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments
      homega heta hdegree false selected
  · have hnext : next ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments
        homega heta hdegree false selected := by
      exact fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive


theorem doubledAlignedBoundarySegments_step_mem_iff_of_state_invariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta))
    (hinvariant : forall y : DoubledAlignedState omega eta,
      y ∈ states ↔
        (doubledAlignedFirstReturnPerm homega heta hdegree).symm y ∈ states)
    (dart : FKMedialBlackDart T) :
    alignedBoundaryPerm homega heta hdegree false dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false states ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree false states := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)
  · let activeArrival : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} :=
      ⟨alignedBoundaryPerm homega heta hdegree false dart, hactive⟩
    let y := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm activeArrival
    have hstep : alignedBoundaryPerm homega heta hdegree false dart =
        doubledAlignedBlackDart homega heta hdegree false y := by
      exact congrArg Subtype.val
        ((doubledAlignedBlackDartEquiv
          homega heta hdegree false).apply_symm_apply activeArrival).symm
    rw [hstep,
      doubledAlignedBlackDart_mem_boundarySegments_iff,
      mem_doubledAlignedBoundarySegments_predecessor_iff
        homega heta hdegree states dart y hstep]
    exact hinvariant y
  · exact mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false states dart hactive

end
end StatMech.FrontierD
