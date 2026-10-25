/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Mathlib.Algebra.Lie.Semisimple.Defs


noncomputable section

open scoped ComplexOrder

structure HarishChandraPair
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K] where
  𝔨 : LieSubalgebra ℂ 𝔤
  Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)

end
