/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part3
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_psi_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 - p) * ptn_psi p false + p * ptn_psi p true = 0 := by
  unfold ptn_psi
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  simp only [ptn_val_false, ptn_val_true]
  field_simp
  ring


theorem ptn_psi_sq_mean {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 - p) * ptn_psi p false ^ 2 + p * ptn_psi p true ^ 2 = 1 := by
  unfold ptn_psi
  have hσ2 : ptn_sigma p ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have hσ : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  simp only [ptn_val_false, ptn_val_true]
  rw [div_pow, div_pow]
  field_simp
  nlinarith [hσ2]


theorem ptn_expect_prod (p : ℝ) (h : ι → Bool → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ∏ e : ι, h e (ω e))
      = ∏ e : ι, ((1 - p) * h e false + p * h e true) := by
  unfold OSSS.expect OSSS.weight OSSS.bernoulliWeight
  have hstep : ∀ ω : ConfigSpace ι,
      (∏ e : ι, (if ω e then p else 1 - p)) * ∏ e : ι, h e (ω e)
        = ∏ e : ι, ((if ω e then p else 1 - p) * h e (ω e)) := by
    intro ω; rw [← Finset.prod_mul_distrib]
  simp_rw [hstep]
  rw [← Fintype.prod_sum (fun (e : ι) (c : Bool) => (if c then p else 1 - p) * h e c)]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring


end StatMech.Probability
