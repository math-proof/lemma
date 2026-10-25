/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

theorem sixVertexGapCorrectionTerm_eq_lambert (lam : ℝ) (n : ℕ) :
    sixVertexGapCorrectionTerm lam n =
      sixVertexGapLambertTerm lam n := by
  rw [sixVertexGapCorrectionTerm, sixVertexGapLambertTerm,
    tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hden :
      1 + Real.exp (-2 * (((n + 1 : ℕ) : ℝ) * lam)) ≠ 0 := by
    positivity
  field_simp [hn, hden]

theorem sixVertexGapCorrectionTerm_norm_le (lam : ℝ) (n : ℕ) :
    ‖sixVertexGapCorrectionTerm lam n‖ ≤
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  let x : ℝ := (n + 1 : ℝ) * lam
  have htanh : Real.tanh x - 1 ≤ 0 := sub_nonpos.mpr (Real.tanh_lt_one x).le
  have hden : 1 ≤ (n + 1 : ℝ) := by norm_num
  rw [sixVertexGapCorrectionTerm, Real.norm_eq_abs, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, abs_of_nonpos htanh,
    abs_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
  simp only [one_mul, neg_sub]
  calc
    (1 - Real.tanh x) / (n + 1 : ℝ)
        ≤ (2 * Real.exp (-2 * x)) / (n + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right
            (one_sub_tanh_le_two_mul_exp_neg_two_mul x) (by positivity)
    _ ≤ 2 * Real.exp (-2 * x) := by
      exact div_le_self (by positivity) hden
    _ = 2 * Real.exp (-2 * lam) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 2
      dsimp [x]
      push_cast
      ring

theorem summable_sixVertexGapCorrectionTerm {lam : ℝ} (hlam : 0 < lam) :
    Summable (sixVertexGapCorrectionTerm lam) := by
  have hq0 : 0 ≤ Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hgeom.of_norm_bounded (sixVertexGapCorrectionTerm_norm_le lam)


end StatMech.FrontierD
