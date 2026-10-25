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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- Existence axiom: a compact symplectic manifold equipped with a compatible
almost complex structure admits a family of approximately-holomorphic sections
that are simultaneously uniformly bounded, approximately holomorphic, uniformly
concentrated, and locally bounded below by Gaussian peaks. -/
class HasGaussianSections
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] where
  sections_exist :
    ∀ (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
      (_hcompat : IsCompatibleACS S J),
    ∃ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
      IsUniformlyBounded fam ∧ IsApproxHolomorphic fam ∧
      IsUniformlyConcentrated fam ∧

      (∃ (pe : PointwiseEval Ω VF) (md : ManifoldDist VF) (c : ℝ), c > 0 ∧
        ∀ (k : ℕ) (p q : VF), md.mdist p q ≤ 1 / Real.sqrt (k : ℝ) →
          c ≤ pe.peval q (fam.section_ k p))


