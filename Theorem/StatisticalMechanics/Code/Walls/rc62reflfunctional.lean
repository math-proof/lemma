/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in


theorem rc62_reflInter_ge_box_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide

open Classical in


theorem rc62_forward_chain_only_bounds_fixpoint
    (boxStart Φstart Φfix reflFix : ℕ)
    (ha : boxStart ≤ Φstart) (hc : Φstart ≤ Φfix) (hb : Φfix ≤ reflFix) :
    boxStart ≤ reflFix :=
  ha.trans (hc.trans hb)

set_option maxRecDepth 4000 in


theorem rc62_forward_chain_strict_gap_fin2 :
    (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 0
    ∧ (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card = 1
    ∧ (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


end StatMech.Walls
