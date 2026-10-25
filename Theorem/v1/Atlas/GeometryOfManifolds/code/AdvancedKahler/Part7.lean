/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part10
set_option autoImplicit false

open DifferentialFormSpace


/-- From the uniform spectral gap, Gaussian decay of $\bar\partial$, and the
$L^2$-bound at $k = 0$, derive the exponential $L^2$-bound for the Green
correction at every $k$:
$\|G(s_{k,p})\|_{L^2} \le C_{L^2}\, e^{-\lambda k^{1/3}}$. -/
theorem correction_l2_exp_bound_from_spectral_gap
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (pde : GreenCorrectionPDEAxioms wdn l2 dol fam) :
    ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (pde.greenCorrection k (fam.section_ k p)) ≤
          C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by

  obtain ⟨C_spec, hC_pos, h_spec⟩ := pde.uniform_spectral_gap

  obtain ⟨C_g, lam, hCg_pos, hlam_pos, h_gauss⟩ := pde.gaussian_decay

  obtain ⟨B, hB_pos, h_zero⟩ := pde.correction_l2_at_zero


  refine ⟨Real.sqrt C_spec * C_g + B, lam, ?_, ?_, ?_⟩
  ·
    exact add_pos (mul_pos (Real.sqrt_pos.mpr hC_pos) hCg_pos) hB_pos
  · exact hlam_pos
  · intro k p
    by_cases hk : k = 0
    ·
      subst hk
      have h0 := h_zero p
      simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0),
        mul_zero, Real.exp_zero, mul_one]
      linarith [mul_pos (Real.sqrt_pos.mpr hC_pos) hCg_pos]
    ·
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
      have h_spec_k := h_spec k hk (fam.section_ k p)
      have h_gauss_k := h_gauss k p

      have h_l2nn := l2.l2norm_nonneg (pde.greenCorrection k (fam.section_ k p))
      have h_delbar_nn := l2.l2norm_nonneg (dol.delbar (fam.section_ k p))
      have hCk_nn : (0 : ℝ) ≤ C_spec / (k : ℝ) := div_nonneg (le_of_lt hC_pos) (le_of_lt hk_pos)
      have h_lin : l2.l2norm (pde.greenCorrection k (fam.section_ k p)) ≤
          Real.sqrt (C_spec / (k : ℝ)) * l2.l2norm (dol.delbar (fam.section_ k p)) :=
        l2_bound_from_squared_bound h_l2nn h_delbar_nn hCk_nn h_spec_k

      have h_sqrt_mono : Real.sqrt (C_spec / (k : ℝ)) ≤ Real.sqrt C_spec := by
        apply Real.sqrt_le_sqrt
        exact div_le_self (le_of_lt hC_pos)
          (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)

      have h_exp_pos := Real.exp_pos (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
      calc l2.l2norm (pde.greenCorrection k (fam.section_ k p))
          ≤ Real.sqrt (C_spec / (k : ℝ)) * l2.l2norm (dol.delbar (fam.section_ k p)) := h_lin
        _ ≤ Real.sqrt C_spec * l2.l2norm (dol.delbar (fam.section_ k p)) := by
            apply mul_le_mul_of_nonneg_right h_sqrt_mono h_delbar_nn
        _ ≤ Real.sqrt C_spec * (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
            apply mul_le_mul_of_nonneg_left h_gauss_k (Real.sqrt_nonneg C_spec)
        _ = Real.sqrt C_spec * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring
        _ ≤ (Real.sqrt C_spec * C_g + B) * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt h_exp_pos)
            linarith

