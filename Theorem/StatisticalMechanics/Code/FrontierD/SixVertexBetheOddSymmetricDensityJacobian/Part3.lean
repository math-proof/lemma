/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheOddPositiveHalfJacobianMatrix_diag_eq_finiteRootDensity
    {N m : Nat} {c : Real} (hN : 0 < N)
    (q : Fin m → Real) (j : Fin m) :
    sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j =
      2 * Real.pi * N * sixVertexFiniteRootDensity c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) (q j) -
        sixVertexBetheOddSymmetricJacobianCorrection c m q j := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  let K : Fin ((m + 1) + m) → Real := fun l =>
    4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
      sixVertexThetaDerivativeDenominator c (p i) (p l)
  have hi : p i = q j := sixVertexOddSymmetricLift_positive m q j
  have hiMem : i ∈ (Finset.univ : Finset (Fin ((m + 1) + m))) :=
    Finset.mem_univ i
  have hsum : (∑ l ∈ (Finset.univ : Finset (Fin ((m + 1) + m))).erase i,
      K l) = (∑ l, K l) - K i := by
    rw [← Finset.sum_erase_add _ _ hiMem]
    ring
  unfold sixVertexBetheOddPositiveHalfJacobianMatrix
  dsimp only
  have hii : i ≠ ir := by
    intro h
    have hv := congrArg Fin.val h
    simp [i, ir, sixVertexOddPositiveIndex,
      sixVertexOddNegativeCoordinateIndex, sixVertexOddNegativeIndex] at hv
    omega
  rw [sixVertexBetheJacobianMatrix, if_pos rfl,
    sixVertexBetheJacobianMatrix, if_neg hii, hsum]
  unfold sixVertexBetheOddSymmetricJacobianCorrection
  dsimp only
  rw [← hi]
  unfold sixVertexFiniteRootDensity
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem norm_sixVertexBetheOddSymmetricJacobianCorrection_le
    {c : Real} (hc : 2 < c) {m : Nat} (q : Fin m → Real) (j : Fin m) :
    ‖sixVertexBetheOddSymmetricJacobianCorrection c m q j‖ ≤
      2 * (sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) := by
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  unfold sixVertexBetheOddSymmetricJacobianCorrection
  dsimp only
  calc
    ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p i) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p ir))‖ ≤
        ‖4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p i)‖ +
        ‖-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
          sixVertexThetaDerivativeDenominator c (p i) (p ir)‖ := norm_add_le _ _
    _ ≤ sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1) +
        sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1) :=
      add_le_add
        (norm_sixVertexTheta_leftDerivative_le hc (p i) (p i))
        (norm_sixVertexTheta_rightDerivative_le hc (p i) (p ir))
    _ = _ := by ring

end
end StatMech.FrontierD
