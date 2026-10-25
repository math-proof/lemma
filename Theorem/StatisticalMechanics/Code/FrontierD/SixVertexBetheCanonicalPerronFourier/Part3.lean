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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem summable_sixVertexAbelLogTermMulRootDensityNorm
    {lam r : Real} (hlam : 0 < lam) (hr : |r| < 1) :
    Summable (fun n : Nat =>
      ‖(sixVertexAbelLogTermMulRootDensityContinuous hlam r n).restrict
        sixVertexRapidityCompact‖) := by
  have hgeom : Summable (fun n : Nat => |r| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  apply (hgeom.mul_right
    (sixVertexFourierRootDensityNormBound lam)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [ContinuousMap.norm_le _
    (mul_nonneg (pow_nonneg (abs_nonneg r) _)
      (sixVertexFourierRootDensityNormBound_nonneg lam))]
  intro alpha
  change ‖(r ^ (n + 1) * Real.cos ((n + 1 : Real) * (alpha : Real)) /
      (n + 1 : Real) * sixVertexFourierRootDensity lam alpha)‖ <= _
  rw [norm_mul]
  apply mul_le_mul
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
    have hcos : |Real.cos ((n + 1 : Real) * (alpha : Real))| <= 1 :=
      abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hden : 1 <= |(n + 1 : Real)| := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    calc
      |r| ^ (n + 1) * |Real.cos ((n + 1 : Real) * (alpha : Real))| /
          |(n + 1 : Real)| <= |r| ^ (n + 1) * 1 / 1 := by
            gcongr
      _ = |r| ^ (n + 1) := by ring
  · exact norm_sixVertexFourierRootDensity_le hlam alpha
  · exact norm_nonneg _
  · exact pow_nonneg (abs_nonneg r) _


theorem intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity
    {lam r : Real} (hlam : 0 < lam) (hr : |r| < 1) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha) =
      ∑' n : Nat, Real.pi * r ^ (n + 1) /
        ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam)) := by
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_sixVertexAbelLogTermMulRootDensityNorm hlam hr)
  have hswap' :
      (∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
        (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
          (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        ∑' n : Nat,
          (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
            (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha := by
    simpa only [sixVertexAbelLogTermMulRootDensityContinuous] using hswap
  rw [show (∫ alpha in -Real.pi..Real.pi,
      sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        ∑' n : Nat,
          (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
            (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha by
    apply intervalIntegral.integral_congr
    intro alpha _
    unfold sixVertexLogCosineSeries
    exact tsum_mul_right.symm]
  rw [← hswap']
  apply tsum_congr
  intro n
  have hcos := intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity
    hlam n 0
  have hcos' :
      (∫ alpha in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * alpha) *
          sixVertexFourierRootDensity lam alpha) =
        Real.pi / Real.cosh ((n + 1 : Real) * lam) := by
    convert hcos using 1 <;> simp [Real.cos_neg]
  simp_rw [show ∀ alpha : Real,
      (r ^ (n + 1) * Real.cos ((n + 1 : Real) * alpha) /
          (n + 1 : Real)) * sixVertexFourierRootDensity lam alpha =
        (r ^ (n + 1) / (n + 1 : Real)) *
          (Real.cos ((n + 1 : Real) * alpha) *
            sixVertexFourierRootDensity lam alpha) by
      intro alpha
      ring]
  rw [intervalIntegral.integral_const_mul, hcos']
  field_simp [(Real.cosh_pos ((n + 1 : Real) * lam)).ne']


end
end StatMech.FrontierD
