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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
set_option autoImplicit false

open DifferentialFormSpace


/-- The symplectic class $[\omega] \in H^2(M, \mathbb{R})$ is integral and
nontrivial: no integer multiple $k\omega$ ($k \neq 0$) is exact. This is the
hypothesis of the Kodaira embedding theorem. -/
class IsIntegralClass
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  not_exact : ∀ (α : Ω 1), inst.d α ≠ S.ω
  smul_not_exact : ∀ (k : ℤ), k ≠ 0 → ∀ (α : Ω 1), inst.d α ≠ k • S.ω


