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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- Derives an exponential $L^2$-bound on the Green correction from a uniform
spectral-gap bound and a Gaussian decay bound on $\bar\partial s_{k,p}$: the
output bound is $\|G(s_{k,p})\|_{L^2} \le C_{L^2} e^{-\lambda k^{1/3}}$. -/
theorem derive_correction_l2_exp_bound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    {l2 : L2NormSpace Ω (inst := inst)}
    {dol : DolbeaultOps (inst := inst)}
    {greenOp : HasGreenOperator Ω l2 dol}
    {fam : ApproxHolomorphicSectionFamily (inst := inst)}

    (c_G : ℝ) (hcG_pos : c_G > 0)
    (h_green_sq : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
      l2.l2norm (greenOp.greenCorrection k s) *
        l2.l2norm (greenOp.greenCorrection k s) ≤
        c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))

    (C_g : ℝ) (lam : ℝ) (hCg_pos : C_g > 0) (hlam_pos : lam > 0)
    (h_gauss : ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))

    (h_zero : ∀ (p : VF),
      l2.l2norm (greenOp.greenCorrection 0 (fam.section_ 0 p)) ≤
        Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))) :
    ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (greenOp.greenCorrection k (fam.section_ k p)) ≤
          C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3)) := by

  refine ⟨Real.sqrt c_G * C_g, lam, mul_pos (Real.sqrt_pos.mpr hcG_pos) hCg_pos, hlam_pos, ?_⟩
  intro k p
  by_cases hk : k = 0
  ·
    subst hk
    convert h_zero p using 2
    simp
  ·

    have h_norm_xi_nn := l2.l2norm_nonneg (greenOp.greenCorrection k (fam.section_ k p))
    have h_norm_ds_nn := l2.l2norm_nonneg (dol.delbar (fam.section_ k p))
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hCk_nn : 0 ≤ c_G / (k : ℝ) := div_nonneg (le_of_lt hcG_pos) (le_of_lt hk_pos)
    have h_sq := h_green_sq k hk (fam.section_ k p)
    have h_linear := l2_bound_from_squared_bound h_norm_xi_nn h_norm_ds_nn hCk_nn h_sq


    have h1_le_k : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have h_div_le : c_G / (k : ℝ) ≤ c_G :=
      div_le_self (le_of_lt hcG_pos) h1_le_k
    have h_sqrt_mono : Real.sqrt (c_G / (k : ℝ)) ≤ Real.sqrt c_G :=
      Real.sqrt_le_sqrt h_div_le

    have h_gauss_k := h_gauss k p

    calc l2.l2norm (greenOp.greenCorrection k (fam.section_ k p))
        ≤ Real.sqrt (c_G / (k : ℝ)) *
            l2.l2norm (dol.delbar (fam.section_ k p)) := h_linear
      _ ≤ Real.sqrt c_G *
            l2.l2norm (dol.delbar (fam.section_ k p)) := by
          apply mul_le_mul_of_nonneg_right h_sqrt_mono h_norm_ds_nn
      _ ≤ Real.sqrt c_G *
            (C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) := by
          apply mul_le_mul_of_nonneg_left h_gauss_k (le_of_lt (Real.sqrt_pos.mpr hcG_pos))
      _ = Real.sqrt c_G * C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)) := by ring

