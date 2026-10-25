/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem norm_sixVertexOffsetCorrectionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetCorrectionTerm lam n alpha‖ <=
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by
  rw [sixVertexOffsetCorrectionTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_pos Real.pi_pos]
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |sixVertexGapCorrectionTerm lam n| / Real.pi *
        |Real.sin ((n + 1 : Real) * alpha)| <=
      ‖sixVertexGapCorrectionTerm lam n‖ / Real.pi * 1 := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hsin (by positivity)
    _ <= (2 * Real.exp (-2 * lam) ^ (n + 1)) / Real.pi := by
      simpa only [mul_one] using div_le_div_of_nonneg_right
        (sixVertexGapCorrectionTerm_norm_le lam n) Real.pi_pos.le
    _ = (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1) := by ring

theorem summable_sixVertexOffsetCorrectionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetCorrectionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      (2 / Real.pi) * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetCorrectionTerm_le lam n alpha)

end
end StatMech.FrontierD
