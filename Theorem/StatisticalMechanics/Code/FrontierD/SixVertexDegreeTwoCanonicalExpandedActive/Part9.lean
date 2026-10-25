/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_activeDart
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
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (doubledAlignedBlackDart homega heta hdegree false x))) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x := by
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer))
      (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) arrival)) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle layer x) := by
  let arrival := (finiteFirstReturn
    (fkMedialBlackBoundaryPerm
      (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer))
    (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
  have hreturn := sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot homega
    heta hdegree middle homegaSector hetaSector hmiddle layer x dart hactive
    hslot
  dsimp only
  unfold sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor
  rw [hreturn]


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) dart)) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x := by
  unfold sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor
  rw [hslot]

theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_of_activeState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))
    (hcolor : sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle layer x) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer))
      (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) dart)) := by
  dsimp only
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart
      hactive hslot,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart
      hslot]
  exact hcolor


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
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
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
    middle homegaSector hetaSector hmiddle x hx
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor,
    ← sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  rw [fkIndexedOccurrenceSlotEquiv_apply_key]
  simp only [Bool.not_false]
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
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
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
    middle homegaSector hetaSector hmiddle x hx
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor,
    ← sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  rw [fkIndexedOccurrenceSlotEquiv_apply_key]
  simp only [Bool.not_true]
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor]
  have hnot : ¬ ∃ i,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle false i =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
    intro hex
    have hrange := (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle false
      (doubledAlignedBlackDart homega heta hdegree false x)).mp (by
        rcases hex with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        calc
          _ = (doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) := hi
          _ = fkColoredBlackDartStrandSlotEquiv
                (alignedRoutingLoopPairing homega heta hdegree false)
                (doubledAlignedBlackDart homega heta hdegree false x) := by
            change _ = fkColoredBlackDartStrandSlotEquiv
              (alignedRoutingLoopPairing homega heta hdegree false)
              (blackDartOfStrandSlot
                (alignedRoutingLoopPairing homega heta hdegree false)
                (doubledAlignedVertex x,
                  doubledAlignedSlot homega heta hdegree false x))
            exact (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
              (alignedRoutingLoopPairing homega heta hdegree false) _).symm)
    exact hx ((doubledAlignedBlackDart_mem_boundarySegments_iff homega heta
      hdegree false _ x).mp hrange)
  rw [fkIndexedOccurrenceSlotEquiv_apply_of_not_routed _ _ _ _ hnot]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor]
  have hcoordinate :
      (doubledAlignedVertex
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree false x) := by
    rw [← sixVertexDegreeTwoTauAdjustedState_trueDart]
    exact (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _).symm
  have hnot : ¬ ∃ i,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true i =
        (doubledAlignedVertex
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) := by
    rw [hcoordinate]
    intro hex
    have hrange := (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle true
      (doubledAlignedBlackDart homega heta hdegree false x)).mp hex
    exact hx ((doubledAlignedBlackDart_mem_boundarySegments_iff homega heta
      hdegree false _ x).mp hrange)
  rw [fkIndexedOccurrenceSlotEquiv_apply_of_not_routed _ _ _ _ hnot]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx,
      sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  · rw [dif_neg hx,
      sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx]


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true x =
      if _hx : sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x := by
  let tx := sixVertexDegreeTwoTauAdjustedState homega heta hdegree x
  by_cases hx : tx ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx]
    have h := sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle tx hx
    simpa [tx] using h
  · rw [dif_neg hx]
    have h := sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle tx hx
    simpa [tx] using h


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true]
  simp


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_input_false_defect
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    (htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree
      middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = false)
    (hpairing :
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false x)) = !x.2 := by
  have hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle false
        (doubledAlignedVertex x) = false := by
    rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState]
    simp [htransition, hx, hpairing]
  have hinput : sixVertexDegreeTwoCanonicalExpandedInputState homega heta
      hdegree middle homegaSector hetaSector hmiddle false x = x := by
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask]
  have htau : sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = x :=
    sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq homega heta hdegree
      x hpairing
  rw [hinput, sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false]
  simp only [hx, dif_pos, htau]
  have hcross := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne homega
    heta hdegree x
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x) =
    (if x.2 then
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) &&
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)
    else
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP ==
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) ||
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)) at hcross
  rw [hpairing] at hcross
  simpa using hcross


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutRight.head hright
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false head =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false predecessor =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
            predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutRight.head hright
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have htransition := cut.rightHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  have hhead : head ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := htransition.1
  have hpredecessor : predecessor ∈
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle := htransition.2
  exact ⟨
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor⟩


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutLeft.head hleft
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false head =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false predecessor =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
            predecessor ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutLeft.head hleft
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have htransition := cut.leftHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  have hhead : head ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := htransition.1
  have hpredecessor : predecessor ∉
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle := htransition.2
  exact ⟨
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor⟩


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree
            rightPredecessor) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false rightHead ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false leftPredecessor =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  have hrightColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hleftColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightFirst :
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          rightPredecessor =
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          rightHead := by
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
      homega heta hdegree rightPredecessor
    simpa [sixVertexDegreeTwoAlignedActiveColor, rightPredecessor, rightHead]
      using h
  have hleftFirst :
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          leftPredecessor =
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          leftHead := by
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
      homega heta hdegree leftPredecessor
    simpa [sixVertexDegreeTwoAlignedActiveColor, leftPredecessor, leftHead]
      using h
  exact ⟨
    hrightColors.2.2.2.trans (hrightFirst.trans hrightColors.1.symm),
    hleftColors.2.1.trans (hleftFirst.trans hleftColors.2.2.1.symm)⟩


theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_network
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    let common :=
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false rightHead
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree
            rightPredecessor) ∧
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle false
          leftPredecessor ∧
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  let common :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
      hdegree middle homegaSector hetaSector hmiddle false rightHead
  have hstitch :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hleftColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightMem : rightHead ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inr (List.head_mem hright)
  have hleftMem : leftHead ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inl (List.head_mem hleft)
  have hstateCycle :
      (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
        rightHead leftHead :=
    alignedPermOrderedAllOrbitLists_sameCycle_of_mem
      (doubledAlignedFirstReturnPerm homega heta hdegree) cut.cut
      (cut.cut_mem homega heta hdegree middle homegaSector hetaSector hmiddle)
      hrightMem hleftMem
  have hfalseCycle := doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
    homega heta hdegree hstateCycle
  have hfalseDartColor :
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false rightHead).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false leftHead).1 := by
    obtain ⟨n, hn⟩ := hfalseCycle.exists_nat_pow_eq
    have hcolor := (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree false).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree false rightHead) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (((alignedBoundaryPerm homega heta hdegree false) ^ n)
            (doubledAlignedBlackDart homega heta hdegree false rightHead)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false rightHead).1 at hcolor
    rw [hn] at hcolor
    exact hcolor.symm
  have hfalse : sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightHead = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        leftHead := by
    rw [sixVertexDegreeTwoAlignedActiveColor,
      sixVertexDegreeTwoAlignedActiveColor,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false rightHead,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false leftHead]
    exact hfalseDartColor
  have hcommonLeft : common =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) :=
    hrightColors.1.trans (hfalse.trans hleftColors.2.2.1.symm)
  exact ⟨hstitch.1.symm,
    hcommonLeft.trans hstitch.2.symm,
    hcommonLeft⟩


theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_rightHead_table
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let v := doubledAlignedVertex (cut.cutRight.head hright)
    let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
        sixVertexDisagreementDart_local_card_eq_two hdegree
          (cut.cutRight.head hright).1
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then !retie.pairingQ else retie.pairingP,
        if selected then !retie.pairingP else retie.pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let v := doubledAlignedVertex (cut.cutRight.head hright)
  let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree
      (cut.cutRight.head hright).1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  simpa [htransition] using htable


theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_leftHead_table
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let v := doubledAlignedVertex (cut.cutLeft.head hleft)
    let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
        sixVertexDisagreementDart_local_card_eq_two hdegree
          (cut.cutLeft.head hleft).1
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then !retie.pairingQ else retie.pairingP,
        if selected then !retie.pairingP else retie.pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let v := doubledAlignedVertex (cut.cutLeft.head hleft)
  let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree
      (cut.cutLeft.head hleft).1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_leftHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  simpa [htransition] using htable


theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let left := cut.cutLeft.head hleft
    left = doubledAlignedBranchSwap right ∧
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false right =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false left ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true right !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true left) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let left := cut.cutLeft.head hleft
  have hbranch : left = doubledAlignedBranchSwap right :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  have hrightMem : right ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inr (List.head_mem hright)
  have hleftMem : left ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inl (List.head_mem hleft)
  have hstateCycle :
      (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
        right left :=
    alignedPermOrderedAllOrbitLists_sameCycle_of_mem
      (doubledAlignedFirstReturnPerm homega heta hdegree) cut.cut
      (cut.cut_mem homega heta hdegree middle homegaSector hetaSector hmiddle)
      hrightMem hleftMem
  have hfalseCycle := doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
    homega heta hdegree hstateCycle
  have hfalseDartColor :
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false left).1 := by
    obtain ⟨n, hn⟩ := hfalseCycle.exists_nat_pow_eq
    have hcolor := (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree false).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree false right) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (((alignedBoundaryPerm homega heta hdegree false) ^ n)
            (doubledAlignedBlackDart homega heta hdegree false right)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 at hcolor
    rw [hn] at hcolor
    exact hcolor.symm
  have hfalse : sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      right = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        left := by
    rw [sixVertexDegreeTwoAlignedActiveColor,
      sixVertexDegreeTwoAlignedActiveColor,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false right,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false left]
    exact hfalseDartColor
  have hfalseSwap :
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex right,
            doubledAlignedSlot homega heta hdegree false right) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex (doubledAlignedBranchSwap right),
            doubledAlignedSlot homega heta hdegree false
              (doubledAlignedBranchSwap right)) := by
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      right = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap right)
    rw [← hbranch]
    exact hfalse
  have htrue :=
    sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq
      homega heta hdegree right hfalseSwap
  refine ⟨hbranch, hfalse, ?_⟩
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
      right != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        left) = true
  rw [hbranch]
  exact htrue

theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
      (cut.cutRight.head hright)
    let leftOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
      (cut.cutLeft.head hleft)
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightOut =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftOut ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightOut !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftOut) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let left := cut.cutLeft.head hleft
  let rightOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer right
  let leftOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer left
  have hcolors := sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
    hvertex
  dsimp only at hcolors
  have houtputs :=
    sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      layer
  change leftOut = doubledAlignedBranchSwap rightOut at houtputs
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightOut = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        leftOut ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightOut !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftOut) =
        true
  rw [houtputs]
  have hfalse := hcolors.2.1
  have htrue := hcolors.2.2
  rw [hcolors.1] at hfalse htrue
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false right =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap right) at hfalse
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true right !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap right)) = true at htrue
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex right) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex right) <;>
    simp [rightOut, sixVertexDegreeTwoCanonicalExpandedOutputState, hmask,
      hparity, hfalse, htrue, bne_comm]

theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_activeReturnSourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutRight.head hright)
    let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutLeft.head hleft)
    let rightReturn :=
      sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false rightPredecessor)
    let leftReturn :=
      sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor)
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightReturn =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftReturn ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightReturn !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftReturn) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutRight.head hright)
  let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutLeft.head hleft)
  let rightReturn :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
      middle homegaSector hetaSector hmiddle false
      (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false rightPredecessor)
  let leftReturn :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
      middle homegaSector hetaSector hmiddle false
      (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false leftPredecessor)
  have hreturns :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hcolors :=
    sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      false
  rcases hreturns with ⟨hrightReturn, hleftReturn⟩
  change rightReturn = sixVertexDegreeTwoCanonicalExpandedOutputState homega
      heta hdegree middle homegaSector hetaSector hmiddle false
        (cut.cutRight.head hright) at hrightReturn
  change leftReturn = sixVertexDegreeTwoCanonicalExpandedOutputState homega
      heta hdegree middle homegaSector hetaSector hmiddle false
        (cut.cutLeft.head hleft) at hleftReturn
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightReturn = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree
        false leftReturn ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightReturn !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftReturn) =
        true
  rw [hrightReturn, hleftReturn]
  dsimp only at hcolors
  exact hcolors


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hy : doubledAlignedFirstReturnPerm homega heta hdegree x ∈
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle
          (doubledAlignedFirstReturnPerm homega heta hdegree x) hy) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
            x)) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  rfl


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_proper_interior
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    (hexit : x ≠ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft.getLast hleft) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
            middle homegaSector hetaSector hmiddle y hy) =
        (doubledAlignedVertex
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  have hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := by
    have hiff := cut.selected_mem_iff homega heta hdegree middle homegaSector
      hetaSector hmiddle hleft hright x
    exact hiff.mpr (Or.inl ⟨hx, hexit⟩)
  exact ⟨hy,
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem homega heta
      hdegree middle homegaSector hetaSector hmiddle x hy⟩

@[simp] theorem sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  rfl


theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_true_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle true rightPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree rightHead) ∧
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle true leftPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  constructor
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simp [sixVertexDegreeTwoCanonicalExpandedSourceReturnState]
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simp [sixVertexDegreeTwoCanonicalExpandedSourceReturnState]


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_emptyCut_sigma
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hempty :
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutLeft = [] \/
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutRight = [])
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
            middle homegaSector hetaSector hmiddle y hy) =
        (doubledAlignedVertex
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  have hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := by
    rcases hempty with hleft | hright
    · exact (cut.selected_invariant_of_left_empty homega heta hdegree middle
        homegaSector hetaSector hmiddle hleft x).mpr hx
    · exact (cut.selected_invariant_of_right_empty homega heta hdegree middle
        homegaSector hetaSector hmiddle hright x).mpr hx
  refine ⟨hy, ?_⟩
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  simp only [sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted]


theorem sixVertexDegreeTwoCanonicalPhysicalExpandedSlotColorInvariant_of_falseDart
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
            (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
              heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
                hdegree middle homegaSector hetaSector hmiddle layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (fkIndexedOccurrenceSlotEquiv
            (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
              heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta
        hdegree middle homegaSector hetaSector hmiddle) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree
    layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart

end
end StatMech.FrontierD
