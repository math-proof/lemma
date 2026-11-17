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
public import Def.v1.Atlas.DifferentialGeometry.code.Manifolds.Part3


public noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsGaussMap (ν : E → E) (M : Set E) : Prop where
  smooth : ContDiffOn ℝ ⊤ ν M
  norm_eq_one : ∀ y ∈ M, ‖ν y‖ = 1
  orthogonal_tangent : ∀ y ∈ M, ∀ ψ : E → ℝ,
    IsLocalDefiningFunction ψ M y →
      ∀ v ∈ tangentSpace ψ y, @inner ℝ _ _ (ν y) v = 0

end Hypersurface
end
