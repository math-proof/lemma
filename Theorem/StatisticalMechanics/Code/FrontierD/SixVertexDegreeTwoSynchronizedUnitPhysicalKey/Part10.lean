/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part9


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (slot : FKLayeredStrandSlot T) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component slot) = slot := by
  exact fkIndexedOccurrenceSlotEquiv_apply_self _ _ _ slot


theorem sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
        hdegree component layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
          component) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence :
        SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component :=
      (Fintype.equivFin
        (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component)).symm i
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
    let occurrence :
        SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
          hdegree component := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)


theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree (!layer) dart) := by
  classical
  let occurrence :
      SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
      hdegree component) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta
          hdegree component currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart := by
    unfold sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv,
    fkIndexedOccurrenceSlotEquiv_apply_key, hkey]


theorem sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)) :
    sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
        component
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree layer dart) := by
  unfold sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart
    ((sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff homega
      heta hdegree component layer dart).mp hexists)


end
end StatMech.FrontierD
