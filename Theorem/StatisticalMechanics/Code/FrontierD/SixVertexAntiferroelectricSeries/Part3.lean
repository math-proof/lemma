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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

theorem one_sub_tanh_le_two_mul_exp_neg_two_mul (x : ℝ) :
    1 - Real.tanh x ≤ 2 * Real.exp (-2 * x) := by
  have hformula : 1 - Real.tanh x =
      2 * Real.exp (-x) / (Real.exp x + Real.exp (-x)) := by
    rw [Real.tanh_eq]
    field_simp
    ring
  rw [hformula]
  have hdiv : Real.exp (-x) / (Real.exp x + Real.exp (-x)) ≤
      Real.exp (-x) / Real.exp x := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  calc
    2 * Real.exp (-x) / (Real.exp x + Real.exp (-x))
        = 2 * (Real.exp (-x) / (Real.exp x + Real.exp (-x))) := by ring
    _ ≤ 2 * (Real.exp (-x) / Real.exp x) := by gcongr
    _ = 2 * Real.exp (-2 * x) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 2
      ring


end StatMech.FrontierD
