/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part28


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
    (hnext : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    seed.boundaryFalseDart layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := seed.retieMask layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    seed.retieMask_inactive layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    seed.retieMask_inactive layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (seed.boundaryFalseDart layer dart) := by
  rw [seed.targetBoundary layer]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer (seed.boundaryFalseDart layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (seed.occurrenceEquiv
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      seed.targetPairing
      (Fintype.card
        (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
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
      (seed.occurrenceEquiv
        (fkColoredLayeredStrandSlotBoundaryPerm seed.targetPairing
          (layer, slot))) = _
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    seed.targetBoundary_slotOfFalseDart layer dart]
  exact hfalseDart layer dart


end
end StatMech.FrontierD
