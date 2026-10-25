/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part27


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_firstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hreturn : seed.ActiveReturnColorInvariant)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, fkColoredBlackDartStrandSlotEquiv
            (seed.targetPairing layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, fkColoredBlackDartStrandSlotEquiv
            (seed.targetPairing layer) dart)) := by
  dsimp only
  rw [seed.firstReturn_slot layer x dart hactive hslot, hslot]
  exact hreturn layer x


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  rw [seed.transportedColor_dart layer dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) := by
  classical
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        seed.splitStates :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false seed.splitStates dart hinactive
  rw [seed.transportedColor_dart layer next,
    seed.transportedColor_dart layer dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false seed.splitStates
  · have hnext : next ∈ doubledAlignedBoundarySegments homega heta hdegree
        false seed.splitStates := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments homega heta hdegree
        false seed.splitStates := fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive


end
end StatMech.FrontierD
