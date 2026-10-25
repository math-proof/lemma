/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc61doubledbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc60reimerinjection.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc61_reimerWprobCore_of_residue (h : rc61_DoubledButterflyResidue) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h


theorem rc61_residue_eq_boxUnionBound : rc61_DoubledButterflyResidue = rc60_BoxUnionBound := rfl


theorem rc61_wall_of_residue (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc60_wall_of_boxUnionBound 𝒜 ℬ h


set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in 


theorem rc61_status :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
        (StatMech.doubleCompress i (StatMech.boxDoubled 𝒜 ℬ)).card = (StatMech.boxDoubled 𝒜 ℬ).card) ∧
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        (rc20_reflInterComp 2 𝒜 ℬ).card
          ≤ (rc20_reflInterComp 2 (rc61_dnA 0 𝒜) (rc61_upB 0 ℬ)).card) ∧
    ((rc20_reflInterComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card
        + (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
      < (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {1}}).card
        + (rc20_famCylBoxComp 2 (rc61_dnA 0 ({∅, {0}} : Finset (Finset (Fin 2)))) (rc61_upB 0 {{0}, {1}})).card) ∧
    (¬ (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}}
        ⊆ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}})) ∧
    (rc61_DoubledButterflyResidue → ReimerWprobCore) :=
  ⟨fun 𝒜 ℬ i => rc61_boxDoubled_card_invariant 𝒜 ℬ i,
   rc61_reflInter_downUp_mono_fin2,
   rc61_gap_not_downUp_mono_fin2,
   rc61_famCylBox_not_subset_reflInter_at_fixpoint_fin2,
   rc61_reimerWprobCore_of_residue⟩

end StatMech.Walls
