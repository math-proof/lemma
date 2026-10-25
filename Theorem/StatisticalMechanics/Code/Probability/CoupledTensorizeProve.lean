/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/CoupledTensorizeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.MasterFamilyProve2.Part2
import Def.StatisticalMechanics.Code.Probability.CoupledTensorizeProve
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS


@[simp] theorem ctp_cfg_zero (a b : Bool) : ctp_cfg a b 0 = a := rfl

@[simp] theorem ctp_cfg_one (a b : Bool) : ctp_cfg a b 1 = b := rfl


theorem ctp_sum_fin2 (g : ConfigSpace (Fin 2) → ℝ) :
    ∑ ω : ConfigSpace (Fin 2), g ω
      = g (ctp_cfg false false) + g (ctp_cfg false true)
        + g (ctp_cfg true false) + g (ctp_cfg true true) := by
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {ctp_cfg false false, ctp_cfg false true, ctp_cfg true false, ctp_cfg true true} := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have h0 := ω 0
    have h1 := ω 1
    by_cases ha : ω 0 <;> by_cases hb : ω 1
    · right; right; right; funext i; fin_cases i <;> simp_all [ctp_cfg]
    · right; right; left; funext i; fin_cases i <;> simp_all [ctp_cfg]
    · right; left; funext i; fin_cases i <;> simp_all [ctp_cfg]
    · left; funext i; fin_cases i <;> simp_all [ctp_cfg]
  have hne : ∀ a b c d : Bool, (a ≠ c ∨ b ≠ d) → ctp_cfg a b ≠ ctp_cfg c d := by
    intro a b c d hcd heq
    rcases hcd with h | h
    · exact h (by have := congrFun heq 0; simpa [ctp_cfg] using this)
    · exact h (by have := congrFun heq 1; simpa [ctp_cfg] using this)
  rw [huniv]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne _ _ _ _ (Or.inr (by decide)), hne _ _ _ _ (Or.inl (by decide)),
          hne _ _ _ _ (Or.inl (by decide))⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne _ _ _ _ (Or.inl (by decide)), hne _ _ _ _ (Or.inl (by decide))⟩)]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact hne _ _ _ _ (Or.inr (by decide)))]
  rw [Finset.sum_singleton]
  ring


theorem ctp_weight (p : ℝ) (a b : Bool) :
    OSSS.weight (OSSS.bernoulliWeight p) (ctp_cfg a b)
      = (if a then p else 1 - p) * (if b then p else 1 - p) := by
  unfold OSSS.weight OSSS.bernoulliWeight
  rw [Fin.prod_univ_two, ctp_cfg_zero, ctp_cfg_one]


theorem ctp_expect_fin2 (p : ℝ) (g : ConfigSpace (Fin 2) → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) g
      = (1 - p) * (1 - p) * g (ctp_cfg false false)
        + (1 - p) * p * g (ctp_cfg false true)
        + p * (1 - p) * g (ctp_cfg true false)
        + p * p * g (ctp_cfg true true) := by
  unfold OSSS.expect
  rw [ctp_sum_fin2]
  simp only [ctp_weight, Bool.false_eq_true, if_false, if_true]


end StatMech.Probability
