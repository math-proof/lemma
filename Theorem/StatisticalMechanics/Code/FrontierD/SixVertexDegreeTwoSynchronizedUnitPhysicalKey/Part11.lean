/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part10


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false
          (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
            component) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component)
  · rw [dif_pos hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply homega heta
        hdegree component layer dart hdart)
  · rw [dif_neg hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
        homega heta hdegree component layer dart hdart)


theorem
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
    hdegree component layer dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl


theorem
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  classical
  let states := sixVertexDegreeTwoSynchronizedComponentStates homega heta
    hdegree component
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments homega heta hdegree false
        states ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false states :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false states dart hinactive
  rw [sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
      hdegree component layer next,
    sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta
      hdegree component layer dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false states
  · have hnext : next ∈ doubledAlignedBoundarySegments homega heta hdegree
        false states := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments homega heta hdegree
        false states := fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive


end
end StatMech.FrontierD
