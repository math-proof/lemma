/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexSymmetricBetheEigenvalueCandidate_eq_value
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) :
    sixVertexSymmetricBetheEigenvalueCandidate c p =
      (sixVertexSymmetricBetheEigenvalueValue c p : ℂ) := by
  unfold sixVertexSymmetricBetheEigenvalueCandidate
  unfold sixVertexSymmetricBetheEigenvalueValue
  simp_rw [sixVertexBetheL_symmetric_pair,
    sixVertexBetheM_symmetric_pair, Complex.normSq_eq_norm_sq]
  push_cast
  ring


theorem sixVertexSymmetricBetheEigenvalueValue_log
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ)
    (hM : ∀ j, sixVertexBetheM c (sixVertexBethePhase (p j)) ≠ 0) :
    Real.log (sixVertexSymmetricBetheEigenvalueValue c p) =
      Real.log 2 +
        2 * ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (p j))‖ := by
  have hnorm (j : Fin k) :
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hM j))
  have hprod :
      (∏ j, ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hnorm j
  rw [sixVertexSymmetricBetheEigenvalueValue,
    Real.log_mul (by norm_num) hprod,
    Real.log_prod (fun j hj => hnorm j)]
  simp_rw [Real.log_pow]
  rw [← Finset.mul_sum]
  norm_num


theorem sixVertexBetheM_phase_ne_zero {c : ℝ} (hc : 2 < c) (p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase p) ≠ 0 := by
  let z := sixVertexBethePhase p
  have hn : ‖z‖ = 1 := sixVertexBethePhase_norm p
  by_cases h1 : z = 1
  · simp [sixVertexBetheM, z, h1]
  · have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    intro hM
    change 1 - (c : ℂ) ^ 2 / (1 - z) = 0 at hM
    field_simp [hden] at hM
    have hM' : 1 - z - (c : ℂ) ^ 2 = 0 := by simpa using hM
    have heq : z = 1 - (c : ℂ) ^ 2 := by
      linear_combination -hM'
    have hre : z.re = 1 - c ^ 2 := by
      have h := congrArg Complex.re heq
      have hcRe : ((c : ℂ) ^ 2).re = c ^ 2 := by
        simp [pow_two]
      simpa only [Complex.sub_re, Complex.one_re, hcRe] using h
    have habs : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [hn, hre] at habs
    have hc2 : 3 < c ^ 2 := by nlinarith
    rw [abs_of_neg (by nlinarith : 1 - c ^ 2 < 0)] at habs
    nlinarith


theorem sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    Real.log (sixVertexSymmetricBetheEigenvalueValue c p) =
      Real.log 2 +
        2 * ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (p j))‖ := by
  exact sixVertexSymmetricBetheEigenvalueValue_log c p
    (fun j => sixVertexBetheM_phase_ne_zero hc (p j))

theorem sixVertexSymmetricBetheEigenvalueValue_pos
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    0 < sixVertexSymmetricBetheEigenvalueValue c p := by
  unfold sixVertexSymmetricBetheEigenvalueValue
  apply mul_pos (by norm_num)
  apply Finset.prod_pos
  intro j hj
  exact pow_pos (norm_pos_iff.mpr
    (sixVertexBetheM_phase_ne_zero hc (p j))) 2


theorem sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal
    {k : ℕ} {c : ℝ} (hc : 2 < c) (p : Fin k → ℝ) :
    (sixVertexSymmetricBetheEigenvalueCandidate c p).im = 0 ∧
      0 < (sixVertexSymmetricBetheEigenvalueCandidate c p).re := by
  rw [sixVertexSymmetricBetheEigenvalueCandidate_eq_value]
  simp [sixVertexSymmetricBetheEigenvalueValue_pos hc p]


theorem sixVertexBetheM_phase_normSq
    (c p : ℝ) (hp : sixVertexBethePhase p ≠ 1) :
    Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) =
      ((c ^ 2 - 1) ^ 2 + 1 +
          2 * (c ^ 2 - 1) * Real.cos p) /
        (2 - 2 * Real.cos p) := by
  let z := sixVertexBethePhase p
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hM : sixVertexBetheM c z =
      (1 - z - (c : ℂ) ^ 2) / (1 - z) := by
    unfold sixVertexBetheM
    field_simp [hden]
  rw [hM, Complex.normSq_div]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  have hzre : z.re = Real.cos p := by
    simp [z, sixVertexBethePhase, Complex.exp_re]
  have hzim : z.im = Real.sin p := by
    simp [z, sixVertexBethePhase, Complex.exp_im]
  have hcRe : ((c : ℂ) ^ 2).re = c ^ 2 := by
    simp [pow_two]
  have hcIm : ((c : ℂ) ^ 2).im = 0 := by
    simp [pow_two]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  rw [hcRe, hcIm, hzre, hzim]
  ring_nf
  rw [Real.sin_sq]
  ring


theorem sixVertexBetheM_phase_log_norm
    (c p : ℝ) (hp : sixVertexBethePhase p ≠ 1) :
    Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖ =
      (1 / 2 : ℝ) * Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos p) /
          (2 - 2 * Real.cos p)) := by
  let w := sixVertexBetheM c (sixVertexBethePhase p)
  calc
    Real.log ‖w‖ = (1 / 2 : ℝ) * (2 * Real.log ‖w‖) := by ring
    _ = (1 / 2 : ℝ) * Real.log (‖w‖ ^ 2) := by
      rw [Real.log_pow]
      norm_num
    _ = (1 / 2 : ℝ) * Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) * Real.cos p) /
          (2 - 2 * Real.cos p)) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * Real.log x)
        (sixVertexBetheM_phase_normSq c p hp)


end StatMech.FrontierD
