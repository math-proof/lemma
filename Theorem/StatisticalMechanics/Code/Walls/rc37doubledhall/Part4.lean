/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc37doubledhall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc37_hallDoubled_iff_hallOneSidedA :
    rc37_HallDoubled ↔ rc33_HallOneSidedA := by
  constructor
  · intro h n 𝒜 ℬ 𝒯 h𝒯
    have := h n 𝒜 ℬ 𝒯 h𝒯
    rwa [rc37_biUnion_admDoubled_card] at this
  · intro h n 𝒜 ℬ 𝒯 h𝒯
    have := h n 𝒜 ℬ 𝒯 h𝒯
    rwa [rc37_biUnion_admDoubled_card]

open Classical in


theorem rc37_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) :
    rc20_FamCylBoxResidue :=
  rc33_famCylBoxResidue_of_hallOneSidedA (rc37_hallDoubled_iff_hallOneSidedA.mp h)

open Classical in


theorem rc37_reimer_closes_of_hallDoubled (h : rc37_HallDoubled) :
    rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc37_hallDoubled_iff_hallOneSidedA.mp h)


open Classical in


theorem rc37_hallDoubled_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 2 𝒜 ℬ)).card := by
  intro 𝒯 h𝒯
  rw [rc37_biUnion_admDoubled_card]
  exact rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ) 𝒯 h𝒯

open Classical in


theorem rc37_hallDoubled_fin3_refuter :
    ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card := by
  intro 𝒯 h𝒯
  rw [rc37_biUnion_admDoubled_card]
  exact rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter 𝒯 h𝒯


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in


theorem rc37_admDoubled_proper_fin3 :
    (rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
      < (boxDoubled rc32_A3 rc32_B3).card := by
  have hle : (rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
      = (rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1}).card := by
    rw [rc37_admDoubled]
    exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)
  rw [hle, card_boxDoubled]
  rw [rc32_A3, rc32_B3]
  decide


set_option linter.unusedVariables false in
open Classical in


theorem rc37_reimer_doubledhall :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
        rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card
            ∧ rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ)
      ∧ (rc37_HallDoubled ↔ rc33_HallOneSidedA)
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card)
      ∧ ((rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
          < (boxDoubled rc32_A3 rc32_B3).card) :=
  ⟨fun n 𝒜 ℬ S => rc37_admOneSidedA_eq_inter n 𝒜 ℬ S,
    fun 𝒜 ℬ => ⟨rc37_complBoxDoubled_card_eq_reflInter 𝒜 ℬ, rc37_complBoxDoubled_subset 𝒜 ℬ⟩,
    rc37_hallDoubled_iff_hallOneSidedA,
    rc37_reimer_closes_of_hallDoubled,
    rc37_hallDoubled_fin3_refuter,
    rc37_admDoubled_proper_fin3⟩

end StatMech.Walls
