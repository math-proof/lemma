/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc25doubledcover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc25_boxDoubledCount_iff_famCylBoxResidue :
    rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    rw [rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ
  · intro h n 𝒜 ℬ
    rw [← rc22_card_reflInter_eq_complPairs]; exact h n 𝒜 ℬ


theorem rc25_cylBoxReflInter_of_boxDoubledCount (h : rc25_BoxDoubledCount) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp
    (rc25_boxDoubledCount_iff_famCylBoxResidue.mp h)


open Classical in


theorem rc25_boxDoubledCount_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc22_complPairs 𝒜 ℬ) := by
  rw [← rc22_card_reflInter_eq_complPairs]
  exact rc20_famCylBox_fin2 𝒜 ℬ


theorem rc25_boxDoubledCount_strict_witness :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}}))
      < #(rc22_complPairs ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) := by
  rw [← rc22_card_reflInter_eq_complPairs, ← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide


open Classical in


theorem rc25_reimer_doubledcover :
    (¬ rc24_BoxDownUpMono)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)), #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)) (S : Finset α),
          (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S)
      ∧ (rc25_BoxDoubledCount ↔ rc20_FamCylBoxResidue)
      ∧ (rc25_BoxDoubledCount → rc18_CylBoxReflInter) :=
  ⟨rc25_boxDownUpMono_false,
    rc25_box_le_dpairs,
    rc25_witness_partition,
    rc25_boxDoubledCount_iff_famCylBoxResidue,
    rc25_cylBoxReflInter_of_boxDoubledCount⟩

end StatMech.Walls
