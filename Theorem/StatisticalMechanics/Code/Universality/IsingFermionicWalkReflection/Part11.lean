/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part12


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


@[simp] theorem reflectPrefix_before
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.before = w.before.map reflectIncrement := rfl

@[simp] theorem reflectPrefix_after
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.after = w.after := rfl

theorem reflectPrefix_length
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.steps.length = w.steps.length := by
  simp [reflectPrefix, steps]

theorem reflectPrefix_valid
    (w : IsingDiagonalWalkHitSplit start level) (hw : w.Valid) :
    w.reflectPrefix.Valid := by
  unfold Valid IsingDiagonalWalkStepsValid at hw ⊢
  intro d hd
  simp only [steps, reflectPrefix, List.mem_append, List.mem_map] at hd
  rcases hd with ⟨e, he, rfl⟩ | hd
  · have heValid := hw e (by
      unfold steps
      exact List.mem_append.mpr (Or.inl he))
    rcases heValid with ⟨hex, hey⟩
    constructor
    · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
    · simpa [reflectIncrement] using hey
  · exact hw d (by
      unfold steps
      exact List.mem_append.mpr (Or.inr hd))


theorem reflectPrefix_firstHit
    (w : IsingDiagonalWalkHitSplit start level) (hw : w.FirstHit) :
    w.reflectPrefix.FirstHit := by
  intro k hk
  have hk' : k < w.before.length := by simpa using hk
  have hbefore := hw k hk'
  simp only [reflectPrefix_before]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint at hbefore ⊢
  rw [displacement_reflectSuffix]
  unfold reflectedEndpoint
  dsimp at hbefore ⊢
  omega


theorem reflectPrefix_endpoint_take_fst_of_le_before
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : k ≤ w.before.length) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k)).1 =
      2 * level -
        (isingDiagonalWalkEndpoint start (w.steps.take k)).1 := by
  have hmap : k ≤ (w.before.map reflectIncrement).length := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append_of_le_length hk,
    List.take_append_of_le_length hmap]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint
  rw [displacement_reflectSuffix]
  unfold reflectedEndpoint
  dsimp
  ring


theorem reflectPrefix_endpoint_take_snd_of_le_before
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : k ≤ w.before.length) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k)).2 =
      (isingDiagonalWalkEndpoint start (w.steps.take k)).2 := by
  have hmap : k ≤ (w.before.map reflectIncrement).length := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append_of_le_length hk,
    List.take_append_of_le_length hmap]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint
  rw [displacement_reflectSuffix]
  rfl


theorem reflectPrefix_endpoint_fst
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint.1 = w.endpoint.1 := by
  unfold endpoint steps isingDiagonalWalkEndpoint reflectPrefix
  rw [displacement_append, displacement_append,
    displacement_reflectSuffix]
  unfold reflectedEndpoint
  have hw := w.hit
  dsimp at hw ⊢
  omega


theorem reflectPrefix_endpoint_snd
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint.2 = w.endpoint.2 := by
  change (reflectedEndpoint level start).2 +
      (isingDiagonalWalkDisplacement
        (w.before.map reflectIncrement ++ w.after)).2 =
    start.2 +
      (isingDiagonalWalkDisplacement (w.before ++ w.after)).2
  rw [displacement_append, displacement_append,
    displacement_reflectSuffix]
  rfl

theorem reflectPrefix_endpoint
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint = w.endpoint := by
  apply Prod.ext
  · exact reflectPrefix_endpoint_fst w
  · exact reflectPrefix_endpoint_snd w

end IsingDiagonalWalkHitSplit
end StatMech.Universality
