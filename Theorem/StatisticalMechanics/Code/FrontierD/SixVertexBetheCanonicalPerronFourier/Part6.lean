/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem summable_sixVertexAbelRootDensitySeriesTerm
    {lam r : Real} (hr : |r| < 1) :
    Summable (sixVertexAbelRootDensitySeriesTerm lam r) := by
  have hgeom : Summable (fun n : Nat => |r| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  apply hgeom.of_norm_bounded
  intro n
  rw [sixVertexAbelRootDensitySeriesTerm, Real.norm_eq_abs, abs_div,
    abs_pow, abs_of_pos (mul_pos (by positivity) (Real.cosh_pos _))]
  have hm : 1 <= (n + 1 : Real) := by norm_num
  have hcosh : 1 <= Real.cosh ((n + 1 : Real) * lam) := by
    exact Real.one_le_cosh _
  have hden : 1 <=
      (n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam) := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ <= (n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam) :=
        mul_le_mul hm hcosh zero_le_one (by linarith [hm])
  rw [div_le_iff₀ (mul_pos (by positivity) (Real.cosh_pos _))]
  exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg r) _) hden


end
end StatMech.FrontierD
