/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)) (j : Fin m) :
    |sixVertexOddPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N ((m + 1) + m)
            (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤
      2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        sixVertexOddPositiveHalfRootGap q j ^ 2 := by
  have hgap := sixVertexOddPositiveHalfRootGap_pos_of_open hopen j
  have hquad := abs_gap_mul_right_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hcount
      (sixVertexOddSymmetricLift m q))
    (show q j - sixVertexOddPositiveHalfRootGap q j ≤ q j by linarith)
  rw [intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    hc hN hsol j] at hquad
  simpa only [sub_sub_cancel] using hquad

theorem abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : (m + 1) + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) x) (j : Fin m) :
    |sixVertexBetheOddPositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤
      sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let mesh := 1 / ((N : Real) * lower)
  let L := (sixVertexFiniteRootDensityLipschitzConstant c : Real)
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hgap : 0 ≤ gap := (sixVertexOddPositiveHalfRootGap_pos_of_open hopen j).le
  have hmesh : gap ≤ mesh :=
    sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity j
  have hcell : |gap * sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) (q j) - 1 / N| ≤
      2 * L * gap ^ 2 :=
    abs_sixVertexOddPositiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
      hc hN hcount hopen hsol j
  have hbase :=
    abs_sixVertexBetheOddPositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le
      hc hN hgap hmesh hcell
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hmesh0 : 0 ≤ mesh := by positivity
  have hsq : gap ^ 2 ≤ mesh ^ 2 := by nlinarith
  unfold sixVertexSymmetricJacobianDiagonalErrorOfLower
  change _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh
  calc
    _ ≤ 2 * Real.pi * N * (2 * L * gap ^ 2) + 2 * R * mesh := hbase
    _ ≤ 4 * Real.pi * N * L * mesh ^ 2 + 2 * R * mesh := by
      have hcoef : 0 ≤ 4 * Real.pi * (N : Real) * L := by positivity
      calc
        2 * Real.pi * N * (2 * L * gap ^ 2) + 2 * R * mesh =
            (4 * Real.pi * N * L) * gap ^ 2 + 2 * R * mesh := by ring
        _ ≤ (4 * Real.pi * N * L) * mesh ^ 2 + 2 * R * mesh :=
          add_le_add (mul_le_mul_of_nonneg_left hsq hcoef) le_rfl
        _ = _ := by ring

theorem sixVertexBetheOddPositiveHalfJacobianMatrix_offdiag_eq_scatteringDerivative
    {N m : Nat} {c : Real} {q : Fin m → Real}
    {j k : Fin m} (hjk : j ≠ k) :
    sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k =
      sixVertexSymmetricScatteringDerivative c (-q j) (-q k) := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let l := sixVertexOddPositiveIndex m k
  let lr := sixVertexOddNegativeCoordinateIndex m k
  have hil : i ≠ l := by
    intro h
    apply hjk
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [i, l, sixVertexOddPositiveIndex] at hv ⊢
    omega
  have hilr : i ≠ lr := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, lr, sixVertexOddPositiveIndex,
      sixVertexOddNegativeCoordinateIndex, sixVertexOddNegativeIndex] at hv
    omega
  have hi : p i = q j := sixVertexOddSymmetricLift_positive m q j
  have hl : p l = q k := sixVertexOddSymmetricLift_positive m q k
  have hlr : p lr = -q k := by
    simp [p, lr, sixVertexOddNegativeCoordinateIndex,
      sixVertexOddSymmetricLift_negative]
  unfold sixVertexBetheOddPositiveHalfJacobianMatrix
  dsimp only
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr]
  simp only [sixVertexOddSymmetricLift_positive]
  rw [show sixVertexOddSymmetricLift m q
      (sixVertexOddNegativeCoordinateIndex m k) = -q k by
        exact hlr]
  unfold sixVertexSymmetricScatteringDerivative
  have hfactor : sixVertexBetheIntegratingFactor c (-q j) =
      sixVertexBetheIntegratingFactor c (q j) := by
    simp [sixVertexBetheIntegratingFactor]
  have hden : sixVertexThetaDerivativeDenominator c (-q j) (-q k) =
      sixVertexThetaDerivativeDenominator c (q j) (q k) := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    simp only [Real.cos_neg, Real.sin_neg]
    ring
  rw [hfactor, hden]
  simp

end
end StatMech.FrontierD
