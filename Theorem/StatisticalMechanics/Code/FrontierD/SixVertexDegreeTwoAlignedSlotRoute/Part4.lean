/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree false dart =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false) dart := by
  rfl

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree true dart =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (alignedBlackDartLayerSwap homega heta hdegree dart) := by
  rfl


theorem sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle))) :
    sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        ((Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i).1 := by
  cases layer <;> rfl


theorem sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) <->
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart] at hi
    have hdart : occurrence.1 = dart := by
      cases layer
      · exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective hi
      · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)


theorem sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle :=
    ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
      homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree currentLayer dart := by
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]


theorem sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)


theorem sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) ↔
      x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle := by
  classical
  cases layer
  · constructor
    · rintro ⟨i, hi⟩
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) occurrence.1 =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) at hi
      have hcoordinate : fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) occurrence.1 =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
            (doubledAlignedBlackDart homega heta hdegree false x) := by
        simpa only [doubledAlignedBlackDart,
          fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot] using hi
      have hdart : occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x :=
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective
            hcoordinate
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) := by
        rw [← hdart]
        exact occurrence.2
      exact (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mp hmem
    · intro hx
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) :=
        (doubledAlignedBlackDart_mem_boundarySegments_iff
          homega heta hdegree false _ x).mpr hx
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        ⟨doubledAlignedBlackDart homega heta hdegree false x, hmem⟩
      let i := Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle) occurrence
      refine ⟨i, ?_⟩
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
            ((Fintype.equivFin
              (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
                middle homegaSector hetaSector hmiddle)).symm i).1 = _
      rw [show (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i = occurrence by
        simp [i]]
      exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x)
  · constructor
    · rintro ⟨i, hi⟩
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree occurrence.1) =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) at hi
      have hcoordinate : fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree occurrence.1) =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
            (doubledAlignedBlackDart homega heta hdegree true x) := by
        simpa only [doubledAlignedBlackDart,
          fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot] using hi
      have hswap : alignedBlackDartLayerSwap homega heta hdegree occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree true x :=
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective
            hcoordinate
      have hdart : occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x := by
        apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        rw [hswap]
        exact (alignedBlackDartLayerSwap_active
          homega heta hdegree x).symm
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) := by
        rw [← hdart]
        exact occurrence.2
      exact (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mp hmem
    · intro hx
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) :=
        (doubledAlignedBlackDart_mem_boundarySegments_iff
          homega heta hdegree false _ x).mpr hx
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        ⟨doubledAlignedBlackDart homega heta hdegree false x, hmem⟩
      let i := Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle) occurrence
      refine ⟨i, ?_⟩
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree
            ((Fintype.equivFin
              (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
                middle homegaSector hetaSector hmiddle)).symm i).1) = _
      rw [show (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i = occurrence by
        simp [i]]
      rw [show occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x by rfl,
        alignedBlackDartLayerSwap_active]
      exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)


end
end StatMech.FrontierD
