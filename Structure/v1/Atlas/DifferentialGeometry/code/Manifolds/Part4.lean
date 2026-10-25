/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.Manifolds.Part3


noncomputable section

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
