/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part2


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpointLoopPartner_eq_anchored (L : List ℤ) :
    hexEndpointLoopPartner L = anchoredLoopReverse L := by
  cases L <;> rfl

theorem hexEndpointLoopPartner_length_of_ne_nil (L : List ℤ)
    (hL : L ≠ []) : (hexEndpointLoopPartner L).length = L.length := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons u tail => simp [hexEndpointLoopPartner, loopReverse_length]

theorem hexEndpointLoopPartner_sum
    (L : List ℤ) (hfirst : ∃ tail, L = 1 :: tail)
    (hsum : L.sum = -4) : (hexEndpointLoopPartner L).sum = 4 := by
  obtain ⟨tail, rfl⟩ := hfirst
  simp only [hexEndpointLoopPartner, List.sum_cons, loopReverse_sum] at hsum ⊢
  omega

@[simp] theorem hexEndpointLoopPartner_involutive (L : List ℤ) :
    hexEndpointLoopPartner (hexEndpointLoopPartner L) = L := by
  rw [hexEndpointLoopPartner_eq_anchored,
    hexEndpointLoopPartner_eq_anchored,
    anchoredLoopReverse_involutive]


end
end StatMech.Universality
