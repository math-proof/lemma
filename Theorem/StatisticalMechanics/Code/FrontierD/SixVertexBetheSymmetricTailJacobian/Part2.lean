/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part2


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) x) (j : Fin m) :
    |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower := by
  let gap := sixVertexPositiveHalfRootGap q j
  let mesh := 1 / ((N : Real) * lower)
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap : 0 ≤ gap :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen j).le
  have hmesh : gap ≤ mesh :=
    sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity j
  have hcell : |gap * sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤
      2 * L * gap ^ 2 :=
    abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
      hc hN hcount hopen hsol j
  have hbase :=
    abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
      hc hN hgap hmesh hcell
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hmesh0 : 0 ≤ mesh := by positivity
  have hsq : gap ^ 2 ≤ mesh ^ 2 := by nlinarith
  unfold sixVertexSymmetricJacobianDiagonalErrorOfLower
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
