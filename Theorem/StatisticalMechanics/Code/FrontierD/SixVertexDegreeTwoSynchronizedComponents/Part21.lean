/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part19


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.unsynchronized_no_vertex_mask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ seed.synchronizedAt d) (mask : Bool) :
    (mask != seed.transitionBit (d, false)) = true ∨
      (mask != seed.transitionBit (d, true)) = true := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt at hunsync
  cases hfalse : seed.transitionBit (d, false) <;>
    cases htrue : seed.transitionBit (d, true) <;>
    cases mask <;> simp_all


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_or_noGo
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.GloballySynchronized ∨
      ∃ d, ∀ mask,
        (mask != seed.transitionBit (d, false)) = true ∨
          (mask != seed.transitionBit (d, true)) = true := by
  classical
  by_cases hsync : seed.GloballySynchronized
  · exact Or.inl hsync
  · right
    rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.GloballySynchronized,
      not_forall] at hsync
    obtain ⟨d, hd⟩ := hsync
    exact ⟨d, seed.unsynchronized_no_vertex_mask d hd⟩


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_adj
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hsync : seed.GloballySynchronized)
    {first second : SixVertexOrientedDisagreementDart omega eta}
    (hadj : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Adj
      first second) :
    seed.selectedDart first = seed.selectedDart second := by
  rcases hadj.2 with ⟨d, endpoints | endpoints⟩
  · rw [endpoints.1, endpoints.2]
    exact (seed.synchronizedAt_iff d).mp (hsync d)
  · rw [endpoints.2, endpoints.1]
    exact ((seed.synchronizedAt_iff d).mp (hsync d)).symm


theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_reachable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (hsync : seed.GloballySynchronized)
    {first second : SixVertexOrientedDisagreementDart omega eta}
    (hreachable :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable
        first second) :
    seed.selectedDart first = seed.selectedDart second := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => rfl
  | tail _ hadj ih =>
      exact ih.trans (seed.selectedDart_eq_of_adj hsync hadj)


theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    seed.GloballySynchronized ↔
      ∀ first second : SixVertexOrientedDisagreementDart omega eta,
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            first =
          (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            second →
        seed.selectedDart first = seed.selectedDart second := by
  constructor
  · intro hsync first second hcomponent
    apply seed.selectedDart_eq_of_reachable hsync
    exact SimpleGraph.ConnectedComponent.exact hcomponent
  · intro hconstant d
    rw [seed.synchronizedAt_iff d]
    apply hconstant
    exact SimpleGraph.ConnectedComponent.sound
      (sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
        homega heta hdegree d)


end
end StatMech.FrontierD
