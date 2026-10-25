/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hN : 0 < N) (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      sixVertexSymmetricTailJacobianDiagonalError c N := by
  let gap := sixVertexPositiveHalfRootGap q j
  let mesh := 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap : 0 ≤ gap :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen j).le
  have hmesh : gap ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_tail hc htail hN hhalf hopen hsol j
  have hcell : |gap * sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤
      2 * L * gap ^ 2 := by
    exact abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
      hc hN (by omega) hopen hsol j
  have hbase :=
    abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
      hc hN hgap hmesh hcell
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hNreal : 0 ≤ (N : Real) := Nat.cast_nonneg N
  have hmesh0 : 0 ≤ mesh := by
    have hfloor := sixVertexTailFiniteDensityFloor_pos hc htail
    positivity
  have hsq : gap ^ 2 ≤ mesh ^ 2 := by nlinarith
  unfold sixVertexSymmetricTailJacobianDiagonalError
  change _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh
  calc
    |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤ 2 * Real.pi * N * (2 * L * gap ^ 2) +
          2 * R * mesh := hbase
    _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh := by
      have hcoef : 0 ≤ 4 * Real.pi * (N : Real) * L := by positivity
      calc
        2 * Real.pi * N * (2 * L * gap ^ 2) + 2 * R * mesh =
            (4 * Real.pi * N * L) * gap ^ 2 + 2 * R * mesh := by ring
        _ ≤ (4 * Real.pi * N * L) * mesh ^ 2 + 2 * R * mesh :=
          add_le_add (mul_le_mul_of_nonneg_left hsq hcoef) le_rfl
        _ = 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh := by ring

end
end StatMech.FrontierD
