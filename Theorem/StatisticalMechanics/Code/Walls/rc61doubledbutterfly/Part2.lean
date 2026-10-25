/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc61doubledbutterfly
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in 


theorem rc61_reflInter_downUp_mono_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 𝒜 ℬ).card
        ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in 


theorem rc61_reflInter_downUp_mono_fin2_coord1 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 𝒜 ℬ).card
        ≤ (rc20_reflInterComp 2 (rc61_dnA 1 𝒜) (rc61_upB 1 ℬ)).card := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in 


theorem rc61_famCylBox_downUp_mono_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 𝒜 ℬ).card
        ≤ (rc20_famCylBoxComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card := by
  decide


set_option maxRecDepth 4000 in


theorem rc61_gap_not_downUp_mono_fin2 :
    (rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card
        + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
      < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
        + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card := by
  decide

set_option maxRecDepth 4000 in


theorem rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2 :
    ¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}
        ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}) := by
  decide

set_option maxRecDepth 4000 in


theorem rc61_fixpoint_witness_is_fixed :
    Down.compression 0 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧
    Down.compression 1 ({∅, {0}} : Finset (Finset (Fin 2))) = {∅, {0}} ∧
    UV.compression {0} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} ∧
    UV.compression {1} ∅ ({{0}, {0, 1}} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide


end StatMech.Walls
