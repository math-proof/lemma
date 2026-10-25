/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
import Def.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in


theorem rc62_fixpoint_wall_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
      (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide


open Classical in


theorem rc62_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 8000000 in


theorem rc62_status :
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    (∀ (Φ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) → ℕ),
        (∀ (i : Fin 2) (p : _), Φ (rc62_step i p) = Φ p) →
        (∀ p, (rc20_famCylBoxComp 2 p.1 p.2).card ≤ Φ p) →
        (∀ p, Φ p ≤ (rc20_reflInterComp 2 p.1 p.2).card) → False) ∧
    ((({∅, {0}} : Finset (Finset (Fin 2))).card * ({∅, {0}} : Finset (Finset (Fin 2))).card) / 4
        > (rc20_reflInterComp 2 ({∅, {0}}) ({∅, {0}})).card) ∧
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨rc62_reflInter_ge_box_fin2,
   rc62_no_invariant_sandwich,
   (rc62_uniform_overshoots_reflInter).1,
   rc62_fixpoint_wall_fin2,
   rc62_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
