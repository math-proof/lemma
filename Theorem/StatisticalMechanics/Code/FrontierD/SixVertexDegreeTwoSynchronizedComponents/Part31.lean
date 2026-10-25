/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part29


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) ->
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
  apply seed.slotColorInvariant_of_falseDart
  intro layer dart
  by_cases hdart : activeBlackDart (omega := omega) (eta := eta) dart
  · exact hactive layer dart (Or.inl hdart)
  · by_cases hnext : activeBlackDart (omega := omega) (eta := eta)
        (alignedBoundaryPerm homega heta hdegree false dart)
    · exact hactive layer dart (Or.inr hnext)
    · rw [seed.boundaryFalseDart_of_inactive layer dart hdart hnext]
      exact seed.transportedColor_falseBoundary_of_inactive layer dart hnext


end
end StatMech.FrontierD
