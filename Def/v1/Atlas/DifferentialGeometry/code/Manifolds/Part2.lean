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
public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part2

@[expose] public section

noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsHypersurfaceSubset (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsSmoothLocalDefiningFunction ψ M y

def IsConvexHypersurface (M : Set E) : Prop :=
  IsHypersurface M ∧
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    (∀ z ∈ M, fderiv ℝ ψ y (z - y) ≤ 0)

end Hypersurface
end
