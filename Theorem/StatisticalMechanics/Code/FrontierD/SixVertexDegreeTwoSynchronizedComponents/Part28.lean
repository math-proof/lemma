/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part26


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false seed.splitStates then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
            heta hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false seed.splitStates
  · rw [dif_pos hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply seed
        layer dart hdart)
  · rw [dif_neg hdart]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem
        seed layer dart hdart)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (seed.occurrenceEquiv
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ seed.splitStates then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x,
    seed.transportedColor_dart]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false seed.splitStates x
  by_cases hx : x ∈ seed.splitStates
  · rw [dif_pos (hmem.mpr hx), dif_pos hx]
    simp
  · rw [dif_neg (fun hdart => hx (hmem.mp hdart)), dif_neg hx]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedActiveColor_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.transportedActiveColor layer x =
      if _hx : x ∈ seed.splitStates then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  exact seed.transportedColor_active layer x


end
end StatMech.FrontierD
