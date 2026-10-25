/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part3
import Def.StatisticalMechanics.Code.Walls.rc63doubledinjection
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc63_dn_eq (i : Fin n) (𝒜 : Finset (Finset (Fin n))) :
    rc63_dn i 𝒜 = rc61_dnA i 𝒜 := rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in


theorem rc63_reflInter_downdown_noninc_fin2 :
    ∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
      (rc20_reflInterComp 2 (rc63_dn 0 𝒜) (rc63_dn 0 ℬ)).card
        ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
  decide

set_option maxRecDepth 4000 in


theorem rc63_box_downdown_decreases_witness :
    (rc20_famCylBoxComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card
        < (rc20_famCylBoxComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card
    ∧ (rc20_reflInterComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card
        = (rc20_reflInterComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card := by
  refine ⟨?_, ?_⟩ <;> decide


end StatMech.Walls
