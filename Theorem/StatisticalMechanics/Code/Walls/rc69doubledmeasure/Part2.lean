/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc69doubledmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc68countmarriage.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc69doubledmeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc69_residue_eq_boxUnionBound : rc69_DoubledMeasureResidue = rc60_BoxUnionBound := rfl


theorem rc69_reimerWprobCore_of_residue (h : rc69_DoubledMeasureResidue) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h


theorem rc69_residue_of_indepHall (h : rc59_IndepHall) : rc69_DoubledMeasureResidue :=
  rc60_boxUnionBound_of_indepHall_global h


open Classical in


theorem rc69_residue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) :=
  rc60_boxUnionBound_fin2 𝒜 ℬ


set_option maxRecDepth 4000 in


theorem rc69_status :
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
        (StatMech.boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card) ∧
    ((StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 3 ∧
      (rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0 ∧
      (rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {0}}).card = 0) ∧
    
    ((rc20_reflInterComp 2 (rc61_dnA 0 ({∅} : Finset (Finset (Fin 2)))) (rc61_upB 0 ({{1}}))).card = 1 ∧
      (rc20_reflInterComp 2 ({∅} : Finset (Finset (Fin 2))) ({{1}})).card = 0) ∧
    (Down.compression 0 ({∅} : Finset (Finset (Fin 2))) = Down.compression 0 ({{0}} : Finset (Finset (Fin 2))) ∧
      ({∅} : Finset (Finset (Fin 2))) ≠ ({{0}} : Finset (Finset (Fin 2)))) ∧
    
    (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
        rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true →
        (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧
    
    (rc69_DoubledMeasureResidue → ReimerWprobCore) :=
  ⟨fun _m 𝒜 ℬ => StatMech.card_boxDoubled_le_mul 𝒜 ℬ,
   ⟨rc69_boxDoubled_unrelated_to_wall.1,
     rc69_boxDoubled_unrelated_to_wall.2.2.1, rc69_boxDoubled_unrelated_to_wall.2.2.2⟩,
   rc69_reflInter_grows_witness,
   rc69_downCompression_not_injective,
   rc69_fixpoint_wall,
   rc69_reimerWprobCore_of_residue⟩

end StatMech.Walls
