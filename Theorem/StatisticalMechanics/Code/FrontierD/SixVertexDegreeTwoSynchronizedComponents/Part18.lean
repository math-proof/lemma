/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part16


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
        seed :=
      (Fintype.equivFin
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)).symm i
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
    let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
        seed := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)


theorem sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card
          (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence
      seed := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart := by
    unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]


theorem sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card
          (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
        (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
        hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart
    ((sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff seed layer
      dart).mp hexists)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.boundary_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree false
        (doubledAlignedBranchSwap x) ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          seed.splitStates ↔
      doubledAlignedBlackDart homega heta hdegree false x ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          seed.splitStates := by
  rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
    doubledAlignedBlackDart_mem_boundarySegments_iff]
  exact seed.branchSwap_mem_splitStates_iff x


end
end StatMech.FrontierD
