/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable def localHorizontalHitReflect
    (t : Nat) (start level target : Int) :
    LocalHorizontalHitFiber t start level target →
      LocalHorizontalHitFiber t (2 * level - start) level target := fun w => by
  let split := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps w.1.1)).get (Option.ne_none_iff_isSome.mp w.2)
  have hsplit : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps w.1.1) = some split :=
    (Option.some_get (Option.ne_none_iff_isSome.mp w.2)).symm
  let split' := split.reflectPrefix
  let bs' := split'.steps.map localHorizontalCode
  have hvalid : split.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsplit]
    exact localHorizontalSteps_valid w.1.1
  have hdecode : localHorizontalSteps bs' = split'.steps :=
    localHorizontalSteps_codes split'.steps (reflectPrefix_valid split hvalid) (by
      intro d hd
      change d ∈ split.before.map reflectIncrement ++ split.after at hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
        simpa [reflectIncrement] using localHorizontalSteps_vertical w.1.1 e
          (by rw [← firstHitSplit_steps hsplit]; exact List.mem_append.mpr (Or.inl he))
      · exact localHorizontalSteps_vertical w.1.1 d
          (by rw [← firstHitSplit_steps hsplit]; exact List.mem_append.mpr (Or.inr hd)))
  refine ⟨⟨bs', ?_, ?_⟩, ?_⟩
  · rw [← localHorizontalSteps_length, hdecode, reflectPrefix_length,
      firstHitSplit_steps hsplit, localHorizontalSteps_length]
    exact w.1.2.1
  · rw [lineFreeEndpoint_localHorizontalSteps, hdecode]
    have horig : split.endpoint.1 = target := by
      unfold IsingDiagonalWalkHitSplit.endpoint
      rw [firstHitSplit_steps hsplit]
      exact (lineFreeEndpoint_localHorizontalSteps w.1.1 start).symm.trans
        w.1.2.2
    exact (reflectPrefix_endpoint_fst split).trans horig
  · change isingDiagonalWalkFirstHitSplit?
      (reflectedEndpoint level (start, 0)) level
        (localHorizontalSteps bs') ≠ none
    rw [hdecode, firstHitSplit_eq_some split'
      (reflectPrefix_firstHit split (firstHitSplit_firstHit hsplit))]
    exact Option.some_ne_none split'

end
end StatMech.Universality
