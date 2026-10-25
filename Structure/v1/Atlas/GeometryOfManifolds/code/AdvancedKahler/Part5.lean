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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
set_option autoImplicit false

open DifferentialFormSpace


/-- The hypothesis that $\bar\partial s_{k,p}$ decays exponentially in
$k^{1/3}$: $\|\bar\partial s_{k,p}\|_{L^2} \le C e^{-\lambda k^{1/3}}$.
This is the form of cutoff-error bound used in Donaldson's argument. -/
structure HasGaussianDecayOfDelbar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  gaussian_decay : ∃ (lam : ℝ) (C : ℝ), lam > 0 ∧ C > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))

/-- Cauchy-type estimates for holomorphic sections: weighted $C^r$ norms of a
holomorphic section $\xi$ (with $\bar\partial \xi = 0$) are controlled by its
$L^2$-norm. -/
structure HasCauchyEstimates
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) : Prop where
  cauchy_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (ξ : Ω 0),
      dol.delbar ξ = 0 →
        wdn.weighted_supnorm k r ξ ≤ C_r * l2.l2norm ξ

/-- Quantitative form of uniform boundedness for a section family with respect
to an explicit weighted derivative sup-norm. -/
structure IsQuantUniformlyBounded
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  deriv_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- Quantitative form of approximate holomorphicity: $\bar\partial$ of each
section is exact and its $L^2$-norm satisfies the explicit $C/\sqrt{k}$ decay
bound. -/
structure IsQuantApproxHolomorphic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (fam.section_ k p) = inst.d β
  delbar_l2_bound : ∃ (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C / Real.sqrt (k : ℝ)

/-- Quantitative form of uniform concentration: distinct base points yield
distinct sections, derivative norms are uniformly bounded, and the sections
exhibit explicit Gaussian decay away from their peak. -/
structure IsQuantUniformlyConcentrated
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q →
    fam.section_ k p ≠ fam.section_ k q
  norm_bounded : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r
  gaussian_decay : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (C_gd lam : ℝ) (N : ℕ),
    C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (fam.section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)


/-- Two families on the same line bundle are exponentially close if all
weighted derivative differences decay like $e^{-\lambda k / 3}$. -/
structure IsExponentiallyClose
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam fam' : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  same_bundle : fam.L = fam'.L
  exp_close_all_derivs : ∃ (lam : ℝ), lam > 0 ∧
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C_r * Real.exp (-lam * (k : ℝ) / 3)


/-- Cube-root version of exponential closeness: the decay rate is
$e^{-\lambda k^{1/3}}$ instead of $e^{-\lambda k}$, which is the
natural rate provided by Donaldson's argument. -/
structure IsExponentiallyCloseCubeRoot
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam fam' : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  same_bundle : fam.L = fam'.L
  exp_close_all_derivs : ∃ (lam : ℝ), lam > 0 ∧
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF),
        wdn.weighted_supnorm k r (fam.section_ k p - fam'.section_ k p) ≤
          C_r * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))

/-- A section family has a uniform local lower bound: each section is nonzero,
its weighted $C^0$ norm is uniformly bounded below, and there is a uniform
lower bound on $|s_{k,p}(q)|$ when $d(p,q) \le 1/\sqrt{k}$ (the natural
scale-$k$ ball). -/
structure HasLocalLowerBound
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  section_nonzero : ∀ (k : ℕ) (p : VF), fam.section_ k p ≠ 0
  lower_bound_exists : ∃ (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k 0 (fam.section_ k p) ≥ c
  ball_lower_bound : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ),
    c > 0 ∧
    ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
      c ≤ pe.peval q (fam.section_ k p)

/-- Hodge orthogonality / harmonic projection: on a compact Kähler manifold,
the Green correction $G(s)$ produced by `kahler_curvature_lower_bound` makes
$s + G(s)$ holomorphic for every $s \in \Omega^0$ and every $k \ne 0$. -/
structure GreenCorrectionInput
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  greenOp : HasGreenOperator Ω l2 dol
  gaussian_decay : ∃ (C_g : ℝ) (lam : ℝ), C_g > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤
        C_g * Real.exp (-lam * (k : ℝ) ^ ((1 : ℝ) / 3))
  cauchy_estimates : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (s : Ω 0),
      wdn.weighted_supnorm k r (greenOp.greenCorrection k s) ≤
        C_r * l2.l2norm (greenOp.greenCorrection k s)
  correction_l2_exp_bound : ∃ (C_l2 : ℝ) (lam_l2 : ℝ), C_l2 > 0 ∧ lam_l2 > 0 ∧
    ∀ (k : ℕ) (p : VF),
      l2.l2norm (greenOp.greenCorrection k (fam.section_ k p)) ≤
        C_l2 * Real.exp (-lam_l2 * (k : ℝ) ^ ((1 : ℝ) / 3))
  hol_at_zero : ∀ (p : VF),
    dol.delbar (fam.section_ 0 p + greenOp.greenCorrection 0 (fam.section_ 0 p)) = 0

  same_bundle_data : LineBundleData (inst := inst)
  corrected_bundle_eq : fam.L = same_bundle_data

