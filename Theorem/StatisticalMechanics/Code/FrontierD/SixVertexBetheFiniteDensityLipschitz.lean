/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityFinite
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexThetaLeftKernelLipschitzBound_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexThetaLeftKernelLipschitzBound c := by
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  dsimp [sixVertexThetaLeftKernelLipschitzBound]
  positivity

theorem sixVertexThetaDerivativeDenominator_uniform_lower
    {c : Real} (hc : 2 < c) (x y : Real) :
    4 * (sixVertexAnisotropyMagnitude c - 1) ^ 2 <=
      sixVertexThetaDerivativeDenominator c x y := by
  let d := sixVertexAnisotropyMagnitude c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hFx := (sixVertexBetheIntegratingFactor_bounds hc x).1
  have hFy := (sixVertexBetheIntegratingFactor_bounds hc y).1
  have hbase : 0 <= d - 1 := sub_nonneg.mpr hd.le
  have hprod : (d - 1) ^ 2 <= Fx * Fy := by
    nlinarith [mul_le_mul hFx hFy hbase
      (sixVertexBetheIntegratingFactor_pos hc x).le]
  rw [sixVertexThetaDerivativeDenominator_eq]
  have hcos := Real.cos_le_one (x - y)
  dsimp [d, Fx, Fy] at hprod ⊢
  nlinarith

theorem sixVertexThetaDerivativeDenominator_lipschitz_left
    {c : Real} (hc : 2 < c) (x z y : Real) :
    |sixVertexThetaDerivativeDenominator c x y -
        sixVertexThetaDerivativeDenominator c z y| <=
      (4 * (sixVertexAnisotropyMagnitude c + 1) + 2) * |x - z| := by
  let d := sixVertexAnisotropyMagnitude c
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fz := sixVertexBetheIntegratingFactor c z
  let Fy := sixVertexBetheIntegratingFactor c y
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hFyPos : 0 <= Fy := (sixVertexBetheIntegratingFactor_pos hc y).le
  have hFyUpper : Fy <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hF : |Fx - Fz| <= |x - z| := by
    simpa [Fx, Fz, sixVertexBetheIntegratingFactor] using
      Real.abs_cos_sub_cos_le x z
  have hcos : |Real.cos (z - y) - Real.cos (x - y)| <= |x - z| := by
    have h := Real.abs_cos_sub_cos_le (z - y) (x - y)
    simpa [abs_sub_comm] using h
  rw [sixVertexThetaDerivativeDenominator_eq,
    sixVertexThetaDerivativeDenominator_eq]
  have heq :
      4 * Fx * Fy + 2 * (1 - Real.cos (x - y)) -
          (4 * Fz * Fy + 2 * (1 - Real.cos (z - y))) =
        4 * (Fx - Fz) * Fy +
          2 * (Real.cos (z - y) - Real.cos (x - y)) := by ring
  rw [show sixVertexBetheIntegratingFactor c x = Fx by rfl,
    show sixVertexBetheIntegratingFactor c z = Fz by rfl,
    show sixVertexBetheIntegratingFactor c y = Fy by rfl,
    heq]
  calc
    |4 * (Fx - Fz) * Fy +
        2 * (Real.cos (z - y) - Real.cos (x - y))| <=
        |4 * (Fx - Fz) * Fy| +
          |2 * (Real.cos (z - y) - Real.cos (x - y))| :=
      abs_add_le _ _
    _ = 4 * |Fx - Fz| * Fy +
        2 * |Real.cos (z - y) - Real.cos (x - y)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hFyPos]
      norm_num
    _ <= (4 * (d + 1) + 2) * |x - z| := by
      have hxz : 0 <= |x - z| := abs_nonneg _
      have h1 := mul_le_mul hF hFyUpper hFyPos hxz
      nlinarith
    _ = (4 * (sixVertexAnisotropyMagnitude c + 1) + 2) *
        |x - z| := by rfl


theorem sixVertexThetaLeftKernel_lipschitz
    {c : Real} (hc : 2 < c) (x z y : Real) :
    |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y -
        4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c z y| <=
      sixVertexThetaLeftKernelLipschitzBound c * |x - z| := by
  let d := sixVertexAnisotropyMagnitude c
  let Fy := sixVertexBetheIntegratingFactor c y
  let Dx := sixVertexThetaDerivativeDenominator c x y
  let Dz := sixVertexThetaDerivativeDenominator c z y
  let L := 4 * (d + 1) + 2
  let q := d - 1
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hq : 0 < q := sub_pos.mpr hd
  have hFyPos : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hFyUpper : Fy <= d + 1 :=
    (sixVertexBetheIntegratingFactor_bounds hc y).2
  have hDxPos : 0 < Dx := sixVertexThetaDerivativeDenominator_pos hc x y
  have hDzPos : 0 < Dz := sixVertexThetaDerivativeDenominator_pos hc z y
  have hDxLower : 4 * q ^ 2 <= Dx := by
    exact sixVertexThetaDerivativeDenominator_uniform_lower hc x y
  have hDzLower : 4 * q ^ 2 <= Dz := by
    exact sixVertexThetaDerivativeDenominator_uniform_lower hc z y
  have hDdiff : |Dx - Dz| <= L * |x - z| := by
    exact sixVertexThetaDerivativeDenominator_lipschitz_left hc x z y
  have hnum : |4 * sixVertexDelta c * Fy| = 4 * d * Fy := by
    have hdelta : sixVertexDelta c = -d := by
      dsimp [d, sixVertexAnisotropyMagnitude]
      ring
    rw [hdelta]
    have hd0 : 0 <= d := hd.le.trans' zero_le_one
    rw [show 4 * -d * Fy = -(4 * d * Fy) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd0) hFyPos.le)]
  have hdenprod : 16 * q ^ 4 <= Dx * Dz := by
    have hmul := mul_le_mul hDxLower hDzLower
      (by positivity : 0 <= 4 * q ^ 2) hDxPos.le
    nlinarith [sq_nonneg (q ^ 2)]
  have hformula :
      4 * sixVertexDelta c * Fy / Dx -
          4 * sixVertexDelta c * Fy / Dz =
        (4 * sixVertexDelta c * Fy) * (Dz - Dx) / (Dx * Dz) := by
    field_simp [hDxPos.ne', hDzPos.ne']
  rw [show sixVertexBetheIntegratingFactor c y = Fy by rfl,
    show sixVertexThetaDerivativeDenominator c x y = Dx by rfl,
    show sixVertexThetaDerivativeDenominator c z y = Dz by rfl,
    hformula, abs_div, abs_mul, abs_of_pos (mul_pos hDxPos hDzPos),
    abs_sub_comm, hnum]
  rw [div_le_iff₀ (mul_pos hDxPos hDzPos)]
  have hleft :
      4 * d * Fy * |Dx - Dz| <=
        4 * d * (d + 1) * L * |x - z| := by
    have hnonneg : 0 <= 4 * d := by positivity
    have hLnonneg : 0 <= L * |x - z| := by
      apply mul_nonneg
      · dsimp [L]
        positivity
      · exact abs_nonneg _
    have hprod := mul_le_mul hDdiff hFyUpper hFyPos.le hLnonneg
    nlinarith
  have hright :
      (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (16 * q ^ 4) <=
        (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (Dx * Dz) := by
    exact mul_le_mul_of_nonneg_left hdenprod (by positivity)
  have hcancel :
      (4 * d * (d + 1) * L / (16 * q ^ 4) * |x - z|) *
          (16 * q ^ 4) =
        4 * d * (d + 1) * L * |x - z| := by
    have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq.ne'
    field_simp
  dsimp [sixVertexThetaLeftKernelLipschitzBound, L, q, d]
  exact hleft.trans (hcancel.symm.trans_le hright)


end
end StatMech.FrontierD
