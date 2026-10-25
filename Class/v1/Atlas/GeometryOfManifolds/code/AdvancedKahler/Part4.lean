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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- An $L^2$-norm structure on differential forms: a seminorm
$\|\cdot\|_{L^2}$ on each $\Omega^p$ satisfying the triangle inequality and
the scaling law $\|r\cdot\alpha\|_{L^2} = |r|\cdot\|\alpha\|_{L^2}$. -/
class L2NormSpace
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  l2norm : ∀ {p : ℕ}, Ω p → ℝ
  l2norm_nonneg : ∀ {p : ℕ} (α : Ω p), 0 ≤ l2norm α
  l2norm_add : ∀ {p : ℕ} (α β : Ω p), l2norm (α + β) ≤ l2norm α + l2norm β
  l2norm_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), l2norm (r • α) = |r| * l2norm α

/-- A scale-weighted $C^r$ sup-norm on sections: for each scale $k$ and order
$r$, a seminorm $\|s\|_{k,r}$ controlling derivatives up to order $r$ with
weights appropriate to the scale-$k$ geometry (used in Donaldson estimates). -/
class WeightedDerivSupNorm
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  weighted_supnorm : (k : ℕ) → (r : ℕ) → Ω 0 → ℝ
  weighted_supnorm_nonneg : ∀ (k r : ℕ) (s : Ω 0), 0 ≤ weighted_supnorm k r s
  weighted_supnorm_add : ∀ (k r : ℕ) (s t : Ω 0),
    weighted_supnorm k r (s + t) ≤ weighted_supnorm k r s + weighted_supnorm k r t
  weighted_supnorm_neg : ∀ (k r : ℕ) (s : Ω 0),
    weighted_supnorm k r (-s) ≤ weighted_supnorm k r s

/-- Pointwise evaluation of $0$-forms (i.e. functions/sections): a map
$(x, s) \mapsto |s(x)|$ taking nonnegative values and bounded by the
weighted $C^0$ sup-norm. -/
class PointwiseEval
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF] where
  peval : VF → Ω 0 → ℝ
  peval_nonneg : ∀ (x : VF) (s : Ω 0), 0 ≤ peval x s
  peval_le_supnorm : ∀ (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (x : VF) (k : ℕ) (s : Ω 0), peval x s ≤ wdn.weighted_supnorm k 0 s

/-- A distance function on the manifold (representing the Riemannian/Kähler
metric distance), satisfying the standard axioms of a pseudo-metric:
nonnegativity, symmetry, $d(p,p) = 0$, and the triangle inequality. -/
class ManifoldDist
    (VF : Type*) where
  mdist : VF → VF → ℝ
  mdist_nonneg : ∀ (p q : VF), 0 ≤ mdist p q
  mdist_symm : ∀ (p q : VF), mdist p q = mdist q p
  mdist_self : ∀ (p : VF), mdist p p = 0
  mdist_triangle : ∀ (p q r : VF), mdist p r ≤ mdist p q + mdist q r

