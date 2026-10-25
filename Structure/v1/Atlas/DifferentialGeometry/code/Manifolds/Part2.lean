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
import Def.v1.Atlas.DifferentialGeometry.code.Manifolds


noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsSmoothLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
    ContDiffOn ℝ ⊤ ψ V ∧
    (∀ x ∈ V, x ∈ M ↔ ψ x = 0) ∧
    (∀ x ∈ V, x ∈ M → fderiv ℝ ψ x ≠ 0)

end Hypersurface
end
