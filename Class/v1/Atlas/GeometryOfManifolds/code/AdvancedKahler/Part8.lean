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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part8
set_option autoImplicit false

open DifferentialFormSpace


/-- Typeclass assumption that `GaussianPeakData` is available for a given
compact symplectic manifold with a compatible almost-complex structure. -/
class HasGaussianPeakData
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst))
    (hcompat : IsCompatibleACS S J) where
  peakData : GaussianPeakData S J hcompat


/-- Abstract Weitzenböck decomposition data on a compact symplectic manifold:
a Green correction, its holomorphicity property, a spectral-gap squared
bound, and a uniform spectral-gap constant $c_G$. -/
class HasWeitzenbockDecomp
    (Ω : ℕ → Type*) {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst)) where
  greenCorrection : ℕ → Ω 0 → Ω 0
  green_holomorphic : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    dol.delbar (s + greenCorrection k s) = 0
  green_l2_sq_bound : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    ∃ (c : ℝ), c > 0 ∧
      l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
        c / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))
  c_G : ℝ
  c_G_pos : c_G > 0
  uniform_l2_bound : ∀ (k : ℕ) (_hk : k ≠ 0) (s : Ω 0),
    l2.l2norm (greenCorrection k s) * l2.l2norm (greenCorrection k s) ≤
      c_G / (k : ℝ) * (l2.l2norm (dol.delbar s) * l2.l2norm (dol.delbar s))


