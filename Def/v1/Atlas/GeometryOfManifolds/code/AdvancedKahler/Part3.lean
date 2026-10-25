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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Assembles a `GreenCorrectionInput` from its constituent estimates:
a Green operator, uniform spectral-gap constant, Gaussian decay of
$\bar\partial$, Cauchy estimates, $k=0$ holomorphicity, and bundle data. -/
noncomputable def buildGreenCorrectionInput
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))

    (greenOp : HasGreenOperator Ω l2 dol)

    (c_G : ℝ) (hcG_pos : c_G > 0)
    (h_green_sq : ∀ (k : ℕ) (hk : k ≠ 0) (s : Ω 0),
      l2.l2norm (greenOp.greenCorrection k s) *
        l2.l2norm (greenOp.greenCorrection k s) ≤
        c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s)))

    (h_gauss : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
      ∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3)))

    (h_cauchy : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (s : Ω 0),
        wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
          C_r * l2.l2norm (greenOp.greenCorrection k s))

    (h_hol_zero : ∀ (p : VF),
      dol.delbar (fam.section_ 0 p + greenOp.greenCorrection 0 (fam.section_ 0 p)) = 0)
    (bundle_data : LineBundleData (inst := inst))
    (h_bundle_eq : fam.L = bundle_data)

    (h_l2_zero : ∀ (C_g : ℝ) (lam : ℝ), C_g > 0 → lam > 0 →
      (∀ (k : ℕ) (p : VF),
        l2.l2norm (dol.delbar (fam.section_ k p)) ≤
          C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))) →
      ∀ (p : VF),
        l2.l2norm (greenOp.greenCorrection 0 (fam.section_ 0 p)) ≤
          Real.sqrt c_G * C_g * Real.exp (-lam * (0 : ℝ) ^ ((1 : ℝ) / 3))) :
    GreenCorrectionInput wdn l2 dol fam where
  greenOp := greenOp
  gaussian_decay := h_gauss
  cauchy_estimates := h_cauchy
  correction_l2_exp_bound := by

    obtain ⟨C_g, lam, hCg_pos, hlam_pos, h_gauss_bound⟩ := h_gauss
    exact derive_correction_l2_exp_bound c_G hcG_pos h_green_sq
      C_g lam hCg_pos hlam_pos h_gauss_bound (h_l2_zero C_g lam hCg_pos hlam_pos h_gauss_bound)
  hol_at_zero := h_hol_zero
  same_bundle_data := bundle_data
  corrected_bundle_eq := h_bundle_eq


