/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part10


namespace StatMech.Onsager

theorem ons_complexNoncriticalDeviation_continuous (beta : ℝ) :
    Continuous (ons_complexNoncriticalDeviation beta) := by
  unfold ons_complexNoncriticalDeviation
  fun_prop

theorem ons_complexCoshNorm_continuous :
    Continuous (fun z : ℂ => ‖Complex.cosh (2 * z)‖) := by
  fun_prop

theorem ons_complexSinhNorm_continuous :
    Continuous (fun z : ℂ => ‖Complex.sinh (2 * z)‖) := by
  fun_prop

theorem ons_complexNoncriticalDeviation_ofReal (beta : ℝ) :
    ons_complexNoncriticalDeviation beta (beta : ℂ) = 0 := by
  have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
  unfold ons_complexNoncriticalDeviation
  rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp

theorem ons_complexNoncriticalNeighborhood_isOpen (beta : ℝ) :
    IsOpen (ons_complexNoncriticalNeighborhood beta) := by
  change IsOpen
    ({z : ℂ | ons_complexNoncriticalDeviation beta z <
        ons_noncriticalGap beta ^ 2 / 2} ∩
      ({z : ℂ | ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1} ∩
       {z : ℂ | ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1}))
  exact (isOpen_lt (ons_complexNoncriticalDeviation_continuous beta) continuous_const).inter
    ((isOpen_lt ons_complexCoshNorm_continuous continuous_const).inter
      (isOpen_lt ons_complexSinhNorm_continuous continuous_const))

theorem ons_complexNoncriticalNeighborhood_mem_nhds {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_complexNoncriticalNeighborhood beta ∈ nhds (beta : ℂ) := by
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hdev : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ons_complexNoncriticalDeviation beta z < ons_noncriticalGap beta ^ 2 / 2 := by
    apply (ons_complexNoncriticalDeviation_continuous beta).continuousAt.eventually_lt
      continuousAt_const
    rw [ons_complexNoncriticalDeviation_ofReal]
    positivity
  have hcosh : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 := by
    apply ons_complexCoshNorm_continuous.continuousAt.eventually_lt continuousAt_const
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    rw [harg, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hsinh : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1 := by
    apply ons_complexSinhNorm_continuous.continuousAt.eventually_lt continuousAt_const
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    rw [harg, ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]
    linarith
  filter_upwards [hdev, hcosh, hsinh] with z hz hc hs
  exact ⟨hz, hc, hs⟩

theorem ons_gIntComplex_sub_ofReal_norm_le_deviation
    (beta : ℝ) (z : ℂ) (k1 k2 : ℝ) :
    ‖ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)‖ ≤
      ons_complexNoncriticalDeviation beta z := by
  let q : ℂ := (Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)
  have hq : ‖q‖ ≤ 2 := by
    calc
      ‖q‖ ≤ ‖(Real.cos k1 : ℂ)‖ + ‖(Real.cos k2 : ℂ)‖ := norm_add_le _ _
      _ = |Real.cos k1| + |Real.cos k2| := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 := by nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  rw [← ons_gIntComplex_ofReal beta k1 k2]
  have heq : ons_gIntComplex z k1 k2 - ons_gIntComplex (beta : ℂ) k1 k2 =
      (Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2) -
        (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q := by
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    unfold ons_gIntComplex q
    rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    ring
  rw [heq]
  calc
    ‖(Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2) -
        (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q‖ ≤
        ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
          ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖ * ‖q‖ := by
            simpa only [norm_mul] using norm_sub_le
              (Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2)
              ((Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q)
    _ ≤ ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
          2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖ := by
      nlinarith [norm_nonneg (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ))]
    _ = ons_complexNoncriticalDeviation beta z := by
      unfold ons_complexNoncriticalDeviation
      ring

theorem ons_gInt_lower_noncritical_base {beta k1 k2 : ℝ}
    (hbeta : 0 < beta) (_hcrit : beta ≠ ons_betaC) :
    ons_noncriticalGap beta ^ 2 ≤ ons_gInt beta k1 k2 := by
  have hs : 0 ≤ Real.sinh (2 * beta) := by
    rw [Real.sinh_nonneg_iff]
    linarith
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hgap : ons_noncriticalGap beta ^ 2 =
      (Real.sinh (2 * beta) - 1) ^ 2 := by
    unfold ons_noncriticalGap
    exact sq_abs _
  rw [hgap]
  exact le_add_of_nonneg_right (mul_nonneg hs hA)

theorem ons_gIntComplex_re_pos_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    0 < (ons_gIntComplex z k1 k2).re := by
  let m : ℝ := ons_noncriticalGap beta ^ 2
  let d : ℂ := ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hm : 0 < m := sq_pos_of_pos hgap
  have hdnorm : ‖d‖ < m / 2 :=
    (ons_gIntComplex_sub_ofReal_norm_le_deviation beta z k1 k2).trans_lt hz.1
  have hdre : -‖d‖ ≤ d.re := by
    exact neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreal := ons_gInt_lower_noncritical_base (k1 := k1) (k2 := k2) hbeta hcrit
  have hre : (ons_gIntComplex z k1 k2).re = ons_gInt beta k1 k2 + d.re := by
    dsimp [d]
    ring_nf
  rw [hre]
  dsimp [m] at hm hdnorm hreal ⊢
  nlinarith

theorem ons_gIntComplex_mem_slitPlane_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ons_gIntComplex z k1 k2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (ons_gIntComplex_re_pos_noncritical hbeta hcrit hz k1 k2)

theorem ons_gIntComplex_norm_lower_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ons_noncriticalGap beta ^ 2 / 2 < ‖ons_gIntComplex z k1 k2‖ := by
  let m : ℝ := ons_noncriticalGap beta ^ 2
  let d : ℂ := ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)
  have hdnorm : ‖d‖ < m / 2 :=
    (ons_gIntComplex_sub_ofReal_norm_le_deviation beta z k1 k2).trans_lt hz.1
  have hdre : -‖d‖ ≤ d.re := by
    exact neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreal := ons_gInt_lower_noncritical_base (k1 := k1) (k2 := k2) hbeta hcrit
  have hre : (ons_gIntComplex z k1 k2).re = ons_gInt beta k1 k2 + d.re := by
    dsimp [d]
    ring_nf
  have hrenorm := Complex.re_le_norm (ons_gIntComplex z k1 k2)
  dsimp [m] at hdnorm hreal ⊢
  rw [hre] at hrenorm
  nlinarith

end StatMech.Onsager
