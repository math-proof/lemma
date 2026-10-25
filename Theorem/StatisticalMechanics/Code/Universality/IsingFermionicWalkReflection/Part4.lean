/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part5


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

theorem reflect_length (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.steps.length = w.steps.length := by
  simp [steps, reflect]

theorem reflect_valid (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.Valid) : w.reflect.Valid := by
  unfold Valid IsingDiagonalWalkStepsValid at hw ⊢
  unfold steps at hw
  intro d hd
  simp only [steps, reflect, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨e, he, rfl⟩
  · exact hw d (List.mem_append.mpr (Or.inl hd))
  · have heValid := hw e (List.mem_append.mpr (Or.inr he))
    rcases heValid with ⟨hex, hey⟩
    constructor
    · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
    · simpa [reflectIncrement] using hey

theorem reflect_firstHit (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.FirstHit) : w.reflect.FirstHit := by
  simpa [FirstHit] using hw

theorem displacement_append (a b : List (Int × Int)) :
    isingDiagonalWalkDisplacement (a ++ b) =
      ((isingDiagonalWalkDisplacement a).1 + (isingDiagonalWalkDisplacement b).1,
        (isingDiagonalWalkDisplacement a).2 + (isingDiagonalWalkDisplacement b).2) := by
  simp [isingDiagonalWalkDisplacement, List.sum_append]

theorem displacement_reflectSuffix (s : List (Int × Int)) :
    isingDiagonalWalkDisplacement (s.map reflectIncrement) =
      (-(isingDiagonalWalkDisplacement s).1,
        (isingDiagonalWalkDisplacement s).2) := by
  have hneg : (s.map (fun d ↦ -d.1)).sum =
      -(s.map Prod.fst).sum := by
    induction s with
    | nil => simp
    | cons d s ih => simp [ih, add_comm]
  unfold isingDiagonalWalkDisplacement
  simp only [List.map_map]
  change ((s.map (fun d ↦ (reflectIncrement d).1)).sum,
    (s.map (fun d ↦ (reflectIncrement d).2)).sum) = _
  simp only [reflectIncrement]
  rw [hneg]


theorem reflect_endpoint_fst (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.endpoint.1 = 2 * level - w.endpoint.1 := by
  rw [show w.reflect.endpoint.1 =
      start.1 + (isingDiagonalWalkDisplacement
        (w.before ++ w.after.map reflectIncrement)).1 by rfl]
  rw [displacement_append, displacement_reflectSuffix]
  unfold endpoint steps isingDiagonalWalkEndpoint
  rw [displacement_append]
  have hw := w.hit
  dsimp at hw ⊢
  omega


theorem reflect_endpoint_snd (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.endpoint.2 = w.endpoint.2 := by
  rw [show w.reflect.endpoint.2 =
      start.2 + (isingDiagonalWalkDisplacement
        (w.before ++ w.after.map reflectIncrement)).2 by rfl]
  rw [displacement_append, displacement_reflectSuffix]
  unfold endpoint steps isingDiagonalWalkEndpoint
  rw [displacement_append]


end IsingDiagonalWalkHitSplit
end StatMech.Universality
