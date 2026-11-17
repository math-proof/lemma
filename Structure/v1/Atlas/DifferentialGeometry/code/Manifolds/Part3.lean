/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
public import Def.v1.Atlas.DifferentialGeometry.code.Manifolds.Part2


public noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsPartialParametrization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : Set E) where
  ambientNhd : Set E
  ambientNhd_open : IsOpen ambientNhd
  paramDomain : Set F
  paramDomain_open : IsOpen paramDomain
  f : F → E
  smooth : ContDiffOn ℝ ⊤ f paramDomain
  injective : Set.InjOn f paramDomain
  image_eq : f '' paramDomain = M ∩ ambientNhd
  immersion : ∀ x ∈ paramDomain, Function.Injective (fderiv ℝ f x)

end Hypersurface
end
