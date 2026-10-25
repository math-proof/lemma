/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
import Def.StatisticalMechanics.Code.Walls.rc39famcyl
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc39_deficit_downDown_strictIncrease :
    (#(rc10_reflInter dc39_A dc39_B) - #(rc20_famCylBox dc39_A dc39_B))
      < (#(rc10_reflInter (Down.compression 0 dc39_A) (Down.compression 0 dc39_B))
          - #(rc20_famCylBox (Down.compression 0 dc39_A) (Down.compression 0 dc39_B))) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq, ← rc20_famCylBoxComp_eq,
    ← rc20_reflInterComp_eq]
  decide


theorem rc39_deficitMono_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
          - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ)))
        ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ))) := by
  intro h
  have := h 3 dc39_A dc39_B 0
  exact absurd this (not_le.mpr rc39_deficit_downDown_strictIncrease)


theorem rc39_famCylBox_oneSide_strictDecrease :
    #(rc20_famCylBox (Down.compression 0 dc39_C) dc39_D)
      < #(rc20_famCylBox dc39_C dc39_D) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide


theorem rc39_boxOneSideMono_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ)) := by
  intro h
  have := h 3 dc39_C dc39_D 0
  exact absurd this (not_le.mpr rc39_famCylBox_oneSide_strictDecrease)


theorem rc39_reflInter_oneSide_strictIncrease :
    #(rc10_reflInter dc39_E dc39_F)
      < #(rc10_reflInter (Down.compression 0 dc39_E) dc39_F) := by
  rw [← rc20_reflInterComp_eq, ← rc20_reflInterComp_eq]
  decide


theorem rc39_reflInter_oneSide_antitone_false :
    ¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
        #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) := by
  intro h
  have := h 3 dc39_E dc39_F 0
  exact absurd this (not_le.mpr rc39_reflInter_oneSide_strictIncrease)


theorem rc39_wall_holds_deficitWitness :
    #(rc20_famCylBox dc39_A dc39_B) ≤ #(rc10_reflInter dc39_A dc39_B) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide


theorem rc39_wall_holds_boxOneSideWitness :
    #(rc20_famCylBox dc39_C dc39_D) ≤ #(rc10_reflInter dc39_C dc39_D) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide


theorem rc39_wall_holds_reflOneSideWitness :
    #(rc20_famCylBox dc39_E dc39_F) ≤ #(rc10_reflInter dc39_E dc39_F) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]; decide


set_option linter.unusedVariables false in
open Classical in


theorem rc39_reimer_famcyl :
    (∀ (𝒜 : Finset (Finset α)), #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ))
      ∧ (∀ (ℬ : Finset (Finset α)), #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ))
      ∧ (∀ {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))},
          (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n))))
            ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n)))) →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          (#(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
            - #(rc20_famCylBox (Down.compression i 𝒜) (Down.compression i ℬ)))
          ≤ (#(rc10_reflInter 𝒜 ℬ) - #(rc20_famCylBox 𝒜 ℬ))))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc20_famCylBox (Down.compression i 𝒜) ℬ)))
      ∧ (¬ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (i : Fin n),
          #(rc10_reflInter (Down.compression i 𝒜) ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))) :=
  ⟨rc39_famCylBox_le_reflInter_right_univ,
    rc39_famCylBox_le_reflInter_left_univ,
    fun {_ _ _} h => rc39_famCylBox_le_reflInter_of_monotone h,
    rc39_deficitMono_false,
    rc39_boxOneSideMono_false,
    rc39_reflInter_oneSide_antitone_false⟩

end StatMech.Walls
