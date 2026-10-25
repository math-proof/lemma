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
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part10
set_option autoImplicit false

open DifferentialFormSpace


/-- The PDE-axioms package for a Green correction operator on a specific
section family: the Green correction, its holomorphicity, the uniform
spectral gap, Gaussian decay of $\bar\partial$, Cauchy estimates, $k=0$
holomorphicity, bundle data, and the $L^2$-bound at $k=0$. -/
structure GreenCorrectionPDEAxioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  greenCorrection : ℕ → Ω 0 → Ω 0
  green_holomorphic : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    dol.delbar (s + greenCorrection k s) = 0
  uniform_spectral_gap : ∃ (C : ℝ), C > 0 ∧ ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
      C / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))
  gaussian_decay : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
  cauchy_estimates : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (s : Ω 0),
      wdn.weighted_supnorm k r (greenCorrection k s) ≤
        C_r * l2.l2norm (greenCorrection k s)
  hol_at_zero : ∀ (p : VF),
    dol.delbar (fam.section_ 0 p + greenCorrection 0 (fam.section_ 0 p)) = 0
  same_bundle_data : LineBundleData (inst := inst)
  corrected_bundle_eq : fam.L = same_bundle_data
  correction_l2_at_zero : ∃ (B : ℝ), B > 0 ∧
    ∀ (p : VF), l2.l2norm (greenCorrection 0 (fam.section_ 0 p)) ≤ B

