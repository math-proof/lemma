/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Def.StatisticalMechanics.Code.Walls.rc10core.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc10_deficitIncInc_of_bkr (h : rc10_BKRSetFamily) : rc10_DeficitBridgeIncInc :=
  fun _ _ _ hA hB => rc10_deficit_incInc_of_bkr h hA hB

open Classical in


theorem rc10_bkr_of_deficitIncInc (h : rc10_DeficitBridgeIncInc) : rc10_BKRSetFamily := by
  intro n 𝒜 ℬ h𝒜 hℬ
  
  set A := familyEvent 𝒜 with hA
  set B := familyEvent ℬ with hB
  have hAinc : IsIncreasing A := by
    intro ω ω' hωω' hω
    simp only [hA, mem_familyEvent] at hω ⊢
    exact h𝒜 (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hBinc : IsIncreasing B := by
    intro ω ω' hωω' hω
    simp only [hB, mem_familyEvent] at hω ⊢
    exact hℬ (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hdef := h n A B hAinc hBinc
  
  have hEA : eventFamily A = 𝒜 := rc10_eventFamily_familyEvent 𝒜
  have hEB : eventFamily B = ℬ := rc10_eventFamily_familyEvent ℬ
  rw [rc5_deficit, rc10_card_box_eq A B hAinc hBinc, rc10_card_reflInter_eq A B, hEA, hEB] at hdef
  have : (#(rc10_boxSupp 𝒜 ℬ) : ℤ) ≤ #(rc10_reflInter 𝒜 ℬ) := by linarith [hdef]
  exact_mod_cast this


theorem rc10_bkr_iff_deficitIncInc : rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc :=
  ⟨rc10_deficitIncInc_of_bkr, rc10_bkr_of_deficitIncInc⟩


theorem rc10_deficitIncInc_of_deficitBridge (h : rc7_DeficitBridge) : rc10_DeficitBridgeIncInc :=
  fun n A B _ _ => h n A B


theorem rc10_deficitBridge_iff_incInc_and_nonmono :
    rc7_DeficitBridge ↔
      (rc10_DeficitBridgeIncInc
        ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
            (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) →
              rc5_deficit A B ≤ 0) := by
  constructor
  · intro h
    exact ⟨rc10_deficitIncInc_of_deficitBridge h, fun n A B _ => h n A B⟩
  · rintro ⟨hII, hNM⟩ n A B
    by_cases hAi : IsIncreasing A
    · by_cases hBi : IsIncreasing B
      · exact hII n A B hAi hBi
      · by_cases hBd : IsDecreasing B
        · exact rc8_deficit_le_zero_inc_dec hAi hBd
        · exact hNM n A B (Or.inr ⟨hBi, hBd⟩)
    · by_cases hAd : IsDecreasing A
      · by_cases hBi : IsIncreasing B
        · exact rc8_deficit_le_zero_dec_inc hAd hBi
        · by_cases hBd : IsDecreasing B
          · exact rc9_decDec_of_incInc (fun {C D} hC hD => hII n C D hC hD) hAd hBd
          · exact hNM n A B (Or.inr ⟨hBi, hBd⟩)
      · exact hNM n A B (Or.inl ⟨hAi, hAd⟩)


theorem rc10_ad_product_bound {β : Type*} [DecidableEq β] (𝒜 ℬ : Finset (Finset β)) :
    #𝒜 * #ℬ ≤ #(𝒜 ⊼ ℬ) * #(𝒜 ⊻ ℬ) :=
  Finset.le_card_infs_mul_card_sups 𝒜 ℬ


open Classical in


theorem rc10_deficit_incInc_one (A B : Set (ConfigSpace (Fin 1)))
    (_ : IsIncreasing A) (_ : IsIncreasing B) : rc5_deficit A B ≤ 0 :=
  rc9_deficit_one A B

open Classical in


theorem rc10_boxSupp_univ {β : Type*} [Fintype β] [DecidableEq β] :
    rc10_boxSupp (univ : Finset (Finset β)) univ = univ := by
  classical
  ext S
  simp only [rc10_boxSupp, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨∅, ∅, Finset.disjoint_empty_left ∅, Finset.empty_subset S, Finset.empty_subset S, trivial⟩


theorem rc10_cardform_setfamily_reduction :
    (rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc)
      ∧ (rc7_DeficitBridge → rc10_DeficitBridgeIncInc)
      ∧ (rc7_DeficitBridge ↔
          (rc10_DeficitBridgeIncInc
            ∧ ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
                (¬ IsIncreasing A ∧ ¬ IsDecreasing A) ∨ (¬ IsIncreasing B ∧ ¬ IsDecreasing B) →
                  rc5_deficit A B ≤ 0)) :=
  ⟨rc10_bkr_iff_deficitIncInc,
    rc10_deficitIncInc_of_deficitBridge,
    rc10_deficitBridge_iff_incInc_and_nonmono⟩

end StatMech.Walls
