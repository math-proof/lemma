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
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part6
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem ptn_qnormPow_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℝ) (f : ConfigSpace ι → ℝ) :
    0 ≤ ptn_qnormPow p q f := by
  unfold ptn_qnormPow OSSS.expect
  exact Finset.sum_nonneg (fun ω _ =>
    mul_nonneg (Finset.prod_nonneg (fun e _ => (bernoulliWeight_isProbWeight hp0 hp1).nonneg e (ω e)))
      (Real.rpow_nonneg (abs_nonneg _) q))

theorem ptn_qnorm_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℝ) (f : ConfigSpace ι → ℝ) :
    0 ≤ ptn_qnorm p q f :=
  Real.rpow_nonneg (ptn_qnormPow_nonneg hp0 hp1 q f) _


theorem ptn_qnorm_rpow_self {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {q : ℝ} (hq : q ≠ 0)
    (f : ConfigSpace ι → ℝ) :
    ptn_qnorm p q f ^ q = ptn_qnormPow p q f := by
  unfold ptn_qnorm
  rw [← Real.rpow_mul (ptn_qnormPow_nonneg hp0 hp1 q f), one_div, inv_mul_cancel₀ hq,
    Real.rpow_one]


end StatMech.Probability
