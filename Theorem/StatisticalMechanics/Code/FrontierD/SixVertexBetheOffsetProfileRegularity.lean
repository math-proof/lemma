/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity


namespace StatMech.FrontierD

noncomputable section

theorem summable_sixVertexOffsetCorrectionLipschitzTerm
    {lam : Real} (hlam : 0 < lam) :
    Summable (sixVertexOffsetCorrectionLipschitzTerm lam) := by
  let q := Real.exp (-2 * lam)
  have hq0 : 0 <= q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hbase := summable_pow_mul_geometric_of_norm_lt_one
    (R := Real) 1 hqnorm
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hscaled := hsucc.mul_left (2 / Real.pi)
  exact hscaled.congr fun n => by
    change (2 / Real.pi) * (((n.succ : Nat) : Real) ^ 1 * q ^ n.succ) =
      (2 / Real.pi) * (n + 1 : Real) * q ^ (n + 1)
    simp only [pow_one, Nat.cast_succ, Nat.succ_eq_add_one]
    ring

theorem sixVertexOffsetCorrectionLipschitzTerm_nonneg
    (lam : Real) (n : Nat) :
    0 <= sixVertexOffsetCorrectionLipschitzTerm lam n := by
  unfold sixVertexOffsetCorrectionLipschitzTerm
  positivity

theorem abs_sixVertexOffsetCorrectionTerm_sub_le
    (lam : Real) (n : Nat) (alpha beta : Real) :
    |sixVertexOffsetCorrectionTerm lam n alpha -
        sixVertexOffsetCorrectionTerm lam n beta| <=
      sixVertexOffsetCorrectionLipschitzTerm lam n * |alpha - beta| := by
  let m : Real := n + 1
  have hm : 0 <= m := by dsimp [m]; positivity
  have hsin :
      |Real.sin (m * alpha) - Real.sin (m * beta)| <=
        m * |alpha - beta| := by
    calc
      |Real.sin (m * alpha) - Real.sin (m * beta)| <=
          |m * alpha - m * beta| := Real.abs_sin_sub_sin_le _ _
      _ = m * |alpha - beta| := by
        rw [show m * alpha - m * beta = m * (alpha - beta) by ring,
          abs_mul, abs_of_nonneg hm]
  have hcoeff := sixVertexGapCorrectionTerm_norm_le lam n
  rw [Real.norm_eq_abs] at hcoeff
  unfold sixVertexOffsetCorrectionTerm
    sixVertexOffsetCorrectionLipschitzTerm
  change |(sixVertexGapCorrectionTerm lam n / Real.pi) *
      Real.sin (m * alpha) -
    (sixVertexGapCorrectionTerm lam n / Real.pi) *
      Real.sin (m * beta)| <= _
  rw [<- mul_sub, abs_mul, abs_div, abs_of_pos Real.pi_pos]
  calc
    |sixVertexGapCorrectionTerm lam n| / Real.pi *
        |Real.sin (m * alpha) - Real.sin (m * beta)| <=
      (2 * Real.exp (-2 * lam) ^ (n + 1)) / Real.pi *
        (m * |alpha - beta|) :=
      mul_le_mul
        (div_le_div_of_nonneg_right hcoeff Real.pi_pos.le) hsin
        (abs_nonneg _) (by positivity)
    _ = (2 / Real.pi) * (n + 1 : Real) *
        Real.exp (-2 * lam) ^ (n + 1) * |alpha - beta| := by
      dsimp [m]
      ring

end
end StatMech.FrontierD
