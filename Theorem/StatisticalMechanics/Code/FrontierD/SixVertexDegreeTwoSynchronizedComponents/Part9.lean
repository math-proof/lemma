/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part8


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.mem_splitStates_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    x ∈ seed.splitStates ↔ x.1 ∈ seed.transitions := by
  rcases x with ⟨dart, branch⟩
  cases branch <;>
    simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.branchSwap_mem_splitStates_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap x ∈ seed.splitStates ↔ x ∈ seed.splitStates := by
  rw [seed.mem_splitStates_iff, seed.mem_splitStates_iff]
  rfl

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_length
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates.length = seed.transitions.length * 2 := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, seed.splitStates_length]
  exact Nat.mul_pos (List.length_pos_of_ne_nil seed.transitions_ne_nil)
    (by norm_num)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.splitStates.Nodup := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates
  rw [List.nodup_flatMap]
  refine ⟨?_, seed.transitions_nodup.imp ?_⟩
  · intro dart hdart
    simp
  · intro first second hne
    simp [List.disjoint_left, hne]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    (doubledAlignedBoundarySegments homega heta hdegree false
      seed.splitStates).Nodup :=
  doubledAlignedBoundarySegments_nodup homega heta hdegree false
    seed.splitStates seed.splitStates_nodup


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.first_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree seed.first = 1 := by
  classical
  exact (Finset.mem_filter.mp seed.first_mem).2.2


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.second_seamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree seed.second = 1 := by
  classical
  exact (Finset.mem_filter.mp seed.second_mem).2.2


end
end StatMech.FrontierD
