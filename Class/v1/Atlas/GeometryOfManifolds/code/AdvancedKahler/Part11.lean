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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
set_option autoImplicit false

open DifferentialFormSpace


/-- Linear-decay variant of the cutoff $\bar\partial$ bound:
$\|\bar\partial s_{k,p}\|_{L^2} \le C_g\, e^{-\lambda k / 3}$. -/
class HasSymplecticHypersurface
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Prop where
  has_holomorphic_peak_sections :
    ∃ (dol : DolbeaultOps (inst := inst))
      (wdn : WeightedDerivSupNorm Ω (inst := inst))
      (k₀ : ℕ) (pe : PointwiseEval Ω VF) (md : ManifoldDist VF)
      (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      1 ≤ k₀ ∧
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧
      (∃ (c : ℝ), c > 0 ∧
        ∀ (k : ℕ), k₀ < k → ∀ (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p)) ∧
      (∃ (fam' : ApproxHolomorphicSectionFamily (inst := inst)),
        IsHolomorphicFamily dol fam' ∧
        IsExponentiallyCloseCubeRoot wdn fam fam')

