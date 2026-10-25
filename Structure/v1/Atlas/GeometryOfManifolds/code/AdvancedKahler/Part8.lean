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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- Bundled "Gaussian peak section" data on a compatibly-almost-complex
symplectic manifold: a line bundle, a section family, and all the analytic
infrastructure (norms, pointwise evaluation, distance) together with the
uniform bound, Gaussian decay, concentration, and local lower-bound estimates
that comprise Donaldson's peak sections. -/
structure GaussianPeakData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (_hcompat : IsCompatibleACS S J) where
  L : LineBundleData (inst := inst)
  section_ : ℕ → VF → Ω 0
  pe : PointwiseEval Ω VF
  md : ManifoldDist VF
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  uniform_bound : ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧
    ∀ (k : ℕ) (p : VF), wdn.weighted_supnorm k r (section_ k p) ≤ C_r
  delbar_exact : ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
    ∃ (β : Ω 0), dol.delbar (section_ k p) = inst.d β
  delbar_l2_decay : ∃ (C : ℝ), C > 0 ∧
    ∀ (dol : DolbeaultOps (inst := inst)) (k : ℕ) (p : VF),
      l2.l2norm (dol.delbar (section_ k p)) ≤ C / Real.sqrt (k : ℝ)
  concentrated : ∀ (k : ℕ) (p q : VF), p ≠ q → section_ k p ≠ section_ k q
  gaussian_decay : ∃ (C_gd lam : ℝ) (N : ℕ), C_gd > 0 ∧ lam > 0 ∧
    ∀ (k : ℕ) (p x : VF),
      pe.peval x (section_ k p) ≤
        C_gd * (1 + (Real.sqrt (↑k) * md.mdist p x) ^ N) *
          Real.exp (-lam * (k : ℝ) * md.mdist p x ^ 2)

  local_lower_bound : ∃ (c : ℝ), c > 0 ∧
    ∀ (k : ℕ) (p q : VF),
      md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) → c ≤ pe.peval q (section_ k p)

