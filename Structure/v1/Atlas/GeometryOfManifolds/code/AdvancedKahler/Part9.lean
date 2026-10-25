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
import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- Cutoff-localized Gaussian decay data: the $\bar\partial$ of the cutoff
peak section satisfies $\|\bar\partial s_{k,p}\|_{L^2} \le A_{\sup}\, k^{1/3}
e^{-\lambda_0 k^{1/3}}$. After absorption (via `absorb_poly_into_exp`) this
becomes the exponential bound used in the Donaldson construction. -/
structure CutoffGaussianData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where
  A_sup : ℝ
  A_sup_pos : A_sup > 0
  lam_0 : ℝ
  lam_0_pos : lam_0 > 0
  l2_delbar_bound : ∀ (k : ℕ) (p : VF),
    l2.l2norm (dol.delbar (fam.section_ k p)) ≤
      A_sup * (k : ℝ) ^ ((1 : ℝ) / 3) * Real.exp (-lam_0 * (k : ℝ) ^ ((1 : ℝ) / 3))

