/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPositiveHalfCellLeftIndex_lt
    {m : Nat} (j : Fin m) :
    sixVertexPositiveHalfCellLeftIndex j < Fin.natAdd m j := by
  unfold sixVertexPositiveHalfCellLeftIndex
  split_ifs with hj
  · rw [Fin.lt_def]
    simp [Fin.castAdd, Fin.natAdd, Fin.rev, hj]
    omega
  · rw [Fin.lt_def]
    simp [Fin.natAdd]
    omega

theorem sixVertexPositiveHalfCellLeftIndex_val_add_one
    {m : Nat} (j : Fin m) :
    (sixVertexPositiveHalfCellLeftIndex j).val + 1 =
      (Fin.natAdd m j).val := by
  unfold sixVertexPositiveHalfCellLeftIndex
  split_ifs with hj
  · simp [Fin.castAdd, Fin.natAdd, Fin.rev, hj]
    omega
  · simp [Fin.natAdd]
    omega

theorem sixVertexEvenSymmetricLift_positiveHalfCellLeft
    {m : Nat} (q : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricLift m q
        (sixVertexPositiveHalfCellLeftIndex j) =
      q j - sixVertexPositiveHalfRootGap q j := by
  unfold sixVertexPositiveHalfCellLeftIndex sixVertexPositiveHalfRootGap
  split_ifs with hj
  · rw [sixVertexEvenSymmetricLift_castAdd]
    simp
    ring
  · rw [sixVertexEvenSymmetricLift_natAdd]
    ring

theorem sixVertexCentralQuantumNumber_positiveHalfCell_sub
    {m : Nat} (j : Fin m) :
    sixVertexCentralQuantumNumber (Fin.natAdd m j) -
        sixVertexCentralQuantumNumber
          (sixVertexPositiveHalfCellLeftIndex j) = 1 := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  have hval := sixVertexPositiveHalfCellLeftIndex_val_add_one j
  have hvalReal :
      ((sixVertexPositiveHalfCellLeftIndex j).val : Real) + 1 =
        ((Fin.natAdd m j).val : Real) := by exact_mod_cast hval
  linarith


theorem intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    ∫ x in q j - sixVertexPositiveHalfRootGap q j..q j,
        sixVertexFiniteRootDensity c N (m + m)
          (sixVertexEvenSymmetricLift m q) x = 1 / N := by
  let p := sixVertexEvenSymmetricLift m q
  let il := sixVertexPositiveHalfCellLeftIndex j
  let ir := Fin.natAdd m j
  have hl : p il = q j - sixVertexPositiveHalfRootGap q j :=
    sixVertexEvenSymmetricLift_positiveHalfCellLeft q j
  have hr : p ir = q j := sixVertexEvenSymmetricLift_natAdd m q j
  rw [← hl, ← hr]
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub hc hN]
  rw [sixVertexBetheCountingFunction_at_root hN hsol ir,
    sixVertexBetheCountingFunction_at_root hN hsol il]
  rw [← sub_div]
  exact congrArg (fun x : Real => x / N)
    (sixVertexCentralQuantumNumber_positiveHalfCell_sub j)


theorem abs_positiveHalfGap_mul_finiteRootDensity_sub_inv_width_le
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    (hcount : m + m ≤ N) {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    |sixVertexPositiveHalfRootGap q j *
          sixVertexFiniteRootDensity c N (m + m)
            (sixVertexEvenSymmetricLift m q) (q j) - 1 / N| ≤
      2 * (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        sixVertexPositiveHalfRootGap q j ^ 2 := by
  have hgap := sixVertexPositiveHalfRootGap_pos_of_open hopen j
  have hquad := abs_gap_mul_right_sub_intervalIntegral_le
    (continuous_sixVertexFiniteRootDensity hc N (m + m)
      (sixVertexEvenSymmetricLift m q))
    (lipschitzWith_sixVertexFiniteRootDensity hc hN hcount
      (sixVertexEvenSymmetricLift m q))
    (show q j - sixVertexPositiveHalfRootGap q j ≤ q j by linarith)
  rw [intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell
    hc hN hsol j] at hquad
  simpa only [sub_sub_cancel] using hquad


theorem sixVertexPositiveHalfRootGap_upper_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    {N m : Nat} (hN : 0 < N) (hhalf : N = 2 * (m + m))
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q)) (j : Fin m) :
    sixVertexPositiveHalfRootGap q j ≤
      1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
  let gap := sixVertexPositiveHalfRootGap q j
  let floor := sixVertexTailFiniteDensityFloor c
  let rho := sixVertexFiniteRootDensity c N (m + m)
    (sixVertexEvenSymmetricLift m q)
  have hgap : 0 ≤ gap :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen j).le
  have hfloor : 0 < floor := sixVertexTailFiniteDensityFloor_pos hc htail
  have hfloorLe (x : Real) : floor ≤ rho x := by
    apply sixVertexTailFiniteDensityFloor_le hc hN
    omega
  have hmono := intervalIntegral.integral_mono_on
    (show q j - gap ≤ q j by linarith)
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (m + m)
      (sixVertexEvenSymmetricLift m q)).intervalIntegrable _ _)
    (fun x _ => hfloorLe x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, sub_sub_cancel] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell
    hc hN hsol j] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  rw [le_div_iff₀ (mul_pos hNreal hfloor)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  have hNinv : (N : Real) * (1 / (N : Real)) = 1 := by
    field_simp [hNreal.ne']
  rw [hNinv] at hmul
  nlinarith


theorem sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hN : 0 < N)
    {q : Fin m → Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) x) (j : Fin m) :
    sixVertexPositiveHalfRootGap q j ≤ 1 / ((N : Real) * lower) := by
  let gap := sixVertexPositiveHalfRootGap q j
  let rho := sixVertexFiniteRootDensity c N (m + m)
    (sixVertexEvenSymmetricLift m q)
  have hgap : 0 ≤ gap :=
    (sixVertexPositiveHalfRootGap_pos_of_open hopen j).le
  have hmono := intervalIntegral.integral_mono_on
    (show q j - gap ≤ q j by linarith)
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (m + m)
      (sixVertexEvenSymmetricLift m q)).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul, sub_sub_cancel] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_positiveHalfCell
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
