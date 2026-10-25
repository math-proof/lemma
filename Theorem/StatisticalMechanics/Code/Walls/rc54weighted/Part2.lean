/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc54weighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc53butterfly.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Def.StatisticalMechanics.Code.Walls.rc54weighted
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc54_wWt_nonneg : ∀ x b, 0 ≤ rc54_wWt x b := by
  intro x b; unfold rc54_wWt; cases b <;> norm_num


theorem rc54_famCylBox_witness :
    rc20_famCylBox rc54_wA rc54_wB = ({∅} : Finset (Finset (Fin 2))) := by
  rw [← rc20_famCylBoxComp_eq, rc54_wA, rc54_wB]; decide


theorem rc54_reflInter_witness :
    rc10_reflInter rc54_wA rc54_wB = ({{0}} : Finset (Finset (Fin 2))) := by
  rw [← rc20_reflInterComp_eq, rc54_wA, rc54_wB]; decide


theorem rc54_fmarg_famCylBox_witness :
    fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB) = 1 := by
  rw [rc54_famCylBox_witness]
  unfold fmarg fwt rc54_wWt
  simp [Finset.sum_singleton]


theorem rc54_fmarg_reflInter_witness :
    fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB) = 1 / 2 := by
  rw [rc54_reflInter_witness]
  unfold fmarg fwt rc54_wWt
  rw [Finset.sum_singleton, Fin.prod_univ_two]
  norm_num


theorem rc54_witness_card_wall :
    (rc20_famCylBox rc54_wA rc54_wB).card ≤ (rc10_reflInter rc54_wA rc54_wB).card := by
  rw [rc54_famCylBox_witness, rc54_reflInter_witness]
  simp


theorem rc54_product_weighted_wall_false :
    ¬ (fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB)
        ≤ fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB)) := by
  rw [rc54_fmarg_famCylBox_witness, rc54_fmarg_reflInter_witness]
  norm_num


theorem rc54_exists_product_weight_refuting_wall :
    ∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))),
      (∀ x b, 0 ≤ w x b)
      ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card
      ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ)) :=
  ⟨rc54_wWt, rc54_wA, rc54_wB, rc54_wWt_nonneg, rc54_witness_card_wall,
    rc54_product_weighted_wall_false⟩


open Classical in


theorem rc54_reimer_of_hallDoubled (h : rc37_HallDoubled) : rc18_CylBoxReflInter :=
  rc37_reimer_closes_of_hallDoubled h

open Classical in


theorem rc54_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) : rc20_FamCylBoxResidue :=
  rc37_famCylBoxResidue_of_hallDoubled h

open Classical in


theorem rc54_reimerWprobCore_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter (rc20_cylBoxReflInter_of_famCylBoxResidue h)


open Classical in


theorem rc54_reimer_weighted_functional :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = (dpairsCount 𝒜 ℬ : ℝ))
      ∧ (∀ (i : Fin 3) (𝒜 ℬ : Finset (Finset (Fin 3))),
          wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((doubleCompress i (boxDoubled 𝒜 ℬ)).card : ℝ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          ((rc10_reflInter 𝒜 ℬ).card : ℝ) ≤ wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ)
      ∧ (∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))),
          (∀ x b, 0 ≤ w x b)
          ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card
          ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ)))
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) :=
  ⟨fun 𝒜 ℬ => rc54_wdpairs_one_eq_dpairsCount 𝒜 ℬ,
    fun i 𝒜 ℬ => rc54_wdpairs_one_butterfly_invariant i 𝒜 ℬ,
    fun 𝒜 ℬ => rc54_reflInter_card_le_wdpairs_one 𝒜 ℬ,
    rc54_exists_product_weight_refuting_wall,
    rc54_reimer_of_hallDoubled,
    rc54_reimerWprobCore_of_famCylBoxResidue⟩

end StatMech.Walls
