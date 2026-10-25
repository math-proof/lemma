/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
    {N m : Nat} {c : Real} (hc : 2 < c) (hN : 0 < N)
    {q : Fin m → Real} {j : Fin m} {E mesh : Real}
    (hgap : 0 ≤ sixVertexOddPositiveHalfRootGap q j)
    (hmesh : sixVertexOddPositiveHalfRootGap q j ≤ mesh)
    (hcell :
      |sixVertexOddPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤ E) :
    |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      2 * Real.pi * N * E +
        2 * (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N ((m + 1) + m)
    (sixVertexOddSymmetricLift m q) (q j)
  let corr := sixVertexBetheOddSymmetricJacobianCorrection c m q j
  have hdiag :=
    sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
      (c := c) hN q j
  have hcorr := norm_sixVertexBetheOddSymmetricJacobianCorrection_le hc q j
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hpi : 0 < 2 * Real.pi := by positivity
  unfold sixVertexBetheOddPositiveHalfScaledJacobianMatrix
  change sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N * rho - corr at hdiag
  rw [hdiag]
  change |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| ≤ _
  have hmain : |2 * Real.pi * N * (gap * rho - 1 / N)| ≤
      2 * Real.pi * N * E := by
    rw [abs_mul, abs_of_pos (mul_pos hpi hNreal)]
    exact mul_le_mul_of_nonneg_left hcell (mul_pos hpi hNreal).le
  have hcorrGap : |corr * gap| ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * mesh := by
    rw [abs_mul, ← Real.norm_eq_abs]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hR : 0 ≤ 2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by positivity
    calc
      ‖corr‖ * |gap| ≤
          (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * |gap| :=
        mul_le_mul_of_nonneg_right hcorr (abs_nonneg gap)
      _ = (2 * (sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1))) * gap := by
        rw [abs_of_nonneg hgap]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmesh hR
  calc
    |(2 * Real.pi * N * rho - corr) * gap - 2 * Real.pi| =
        |2 * Real.pi * N * (gap * rho - 1 / N) - corr * gap| := by
      field_simp
      ring
    _ ≤ |2 * Real.pi * N * (gap * rho - 1 / N)| + |corr * gap| :=
      abs_sub _ _
    _ ≤ _ := add_le_add hmain hcorrGap

end
end StatMech.FrontierD
