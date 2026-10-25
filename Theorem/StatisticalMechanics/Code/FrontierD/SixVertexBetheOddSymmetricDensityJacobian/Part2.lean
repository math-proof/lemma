/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddPositiveHalfCellLeftIndex_val_add_one
    {m : Nat} (j : Fin m) :
    (sixVertexOddPositiveHalfCellLeftIndex j).val + 1 =
      (sixVertexOddPositiveIndex m j).val := by
  unfold sixVertexOddPositiveHalfCellLeftIndex
  split_ifs with hj
  · simp [sixVertexOddCentralIndex, sixVertexOddPositiveIndex, hj]
  · simp [sixVertexOddPositiveIndex]
    omega

theorem sixVertexOddSymmetricLift_positiveHalfCellLeft
    {m : Nat} (q : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricLift m q
        (sixVertexOddPositiveHalfCellLeftIndex j) =
      q j - sixVertexOddPositiveHalfRootGap q j := by
  unfold sixVertexOddPositiveHalfCellLeftIndex
    sixVertexOddPositiveHalfRootGap
  split_ifs with hj
  · rw [sixVertexOddSymmetricLift_central]
    ring
  · rw [sixVertexOddSymmetricLift_positive]
    ring

theorem sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub
    {m : Nat} (j : Fin m) :
    sixVertexCentralQuantumNumber (sixVertexOddPositiveIndex m j) -
        sixVertexCentralQuantumNumber
          (sixVertexOddPositiveHalfCellLeftIndex j) = 1 := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  have hval := sixVertexOddPositiveHalfCellLeftIndex_val_add_one j
  have hvalReal :
      ((sixVertexOddPositiveHalfCellLeftIndex j).val : Real) + 1 =
        ((sixVertexOddPositiveIndex m j).val : Real) := by exact_mod_cast hval
  linarith

theorem intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)) (j : Fin m) :
    ∫ x in q j - sixVertexOddPositiveHalfRootGap q j..q j,
        sixVertexFiniteRootDensity c N ((m + 1) + m)
          (sixVertexOddSymmetricLift m q) x = 1 / N := by
  let p := sixVertexOddSymmetricLift m q
  let il := sixVertexOddPositiveHalfCellLeftIndex j
  let ir := sixVertexOddPositiveIndex m j
  have hl : p il = q j - sixVertexOddPositiveHalfRootGap q j :=
    sixVertexOddSymmetricLift_positiveHalfCellLeft q j
  have hr : p ir = q j := sixVertexOddSymmetricLift_positive m q j
  rw [← hl, ← hr,
    intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub hc hN,
    sixVertexBetheCountingFunction_at_root hN hsol ir,
    sixVertexBetheCountingFunction_at_root hN hsol il, ← sub_div]
  exact congrArg (fun x : Real => x / N)
    (sixVertexCentralQuantumNumber_oddPositiveHalfCell_sub j)

theorem sixVertexOddPositiveHalfRootGap_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexOddSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q) x) (j : Fin m) :
    sixVertexOddPositiveHalfRootGap q j ≤ 1 / ((N : Real) * lower) := by
  let gap := sixVertexOddPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N ((m + 1) + m)
    (sixVertexOddSymmetricLift m q)
  have hgap : 0 ≤ gap := (sixVertexOddPositiveHalfRootGap_pos_of_open hopen j).le
  have hmono := intervalIntegral.integral_mono_on
    (show q j - gap ≤ q j by linarith)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N ((m + 1) + m)
      (sixVertexOddSymmetricLift m q)).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, sub_sub_cancel] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_oddPositiveHalfCell
    hc hN hsol j] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith

end
end StatMech.FrontierD
