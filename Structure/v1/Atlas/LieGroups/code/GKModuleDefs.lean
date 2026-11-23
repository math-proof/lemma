/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.GKModule.Part2
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Theorem.LinearMap.EqContinuousLinearEquivOfBijective.of.Bijective
public import Mathlib.Algebra.Lie.Semisimple.Defs


public noncomputable section

open scoped ComplexOrder

structure HarishChandraPair
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K] where
  𝔨 : LieSubalgebra ℂ 𝔤
  Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)

end
