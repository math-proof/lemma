module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part4
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

theorem tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div (x : ℝ) :
    Real.tanh x - 1 =
      -2 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x)) := by
  rw [Real.tanh_eq]
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  have hqden : 1 + Real.exp (-2 * x) ≠ 0 := by positivity
  have hcore : Real.exp x * Real.exp (-(x * 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [hexp, hden, hqden]
  nlinarith [hcore]


end StatMech.FrontierD
