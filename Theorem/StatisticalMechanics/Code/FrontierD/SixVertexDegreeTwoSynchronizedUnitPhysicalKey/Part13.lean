/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part12


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor homega heta
        hdegree component layer x =
      if sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
          hdegree component x then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false
      (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree
        component) x
  by_cases hx : sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega
      heta hdegree component x = true
  · rw [if_pos hx,
      sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply homega heta
        hdegree component layer _
        (hmem.mpr (sixVertexDegreeTwoSynchronizedComponent_mem_states_iff
          homega heta hdegree component x |>.mpr hx))]
    simp [sixVertexDegreeTwoAlignedActiveColor]
  · have hxBool :
        sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
          hdegree component x = false := Bool.eq_false_of_not_eq_true hx
    rw [if_neg hx,
      sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem
        homega heta hdegree component layer _
        (fun hdart => hx
          ((sixVertexDegreeTwoSynchronizedComponent_mem_states_iff homega heta
            hdegree component x).mp (hmem.mp hdart)))]
    simp [sixVertexDegreeTwoAlignedActiveColor]


end
end StatMech.FrontierD
