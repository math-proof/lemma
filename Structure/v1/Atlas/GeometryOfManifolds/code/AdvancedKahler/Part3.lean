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
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- A section family is uniformly bounded if its derivatives in every weighted
$C^r$ norm are bounded uniformly in $k$ and $p$. -/
structure IsUniformlyBounded
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  deriv_bounded : ∃ (wdn : WeightedDerivSupNorm Ω (inst := inst)),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- A section family is approximately holomorphic: $\bar\partial s_{k,p}$ is
exact and its $L^2$-norm decays like $1/\sqrt{k}$, which is the precise
Donaldson approximate-holomorphicity condition. -/
structure IsApproxHolomorphic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (fam.section_ k p) = inst.d β
  delbar_l2_decay : ∃ (l2 : L2NormSpace Ω (inst := inst)) (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (fam.section_ k p)) ≤ C / Real.sqrt (k : ℝ)

/-- A section family is uniformly concentrated: distinct base points give
distinct sections, the sections exhibit Gaussian decay
$|s_{k,p}(x)| \lesssim (1 + \sqrt{k}\,d(p,x))^N e^{-\lambda k\, d(p,x)^2}$
away from $p$, and derivative norms are uniformly bounded. -/
structure IsUniformlyConcentrated
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q → fam.section_ k p ≠ fam.section_ k q
  gaussian_decay : ∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (C_gd lam : ℝ) (N : ℕ),
    C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (fam.section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)
  deriv_norm_bounded : ∃ (wdn : WeightedDerivSupNorm Ω (inst := inst)),
    ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
      ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (fam.section_ k p) ≤ C_r

/-- A section family is genuinely holomorphic if $\bar\partial s_{k,p} = 0$
for every $k$ and $p$. -/
structure IsHolomorphicFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) : Prop where
  holomorphic : ∀ (k : ℕ) (p : VF),
    dol.delbar (fam.section_ k p) = 0


