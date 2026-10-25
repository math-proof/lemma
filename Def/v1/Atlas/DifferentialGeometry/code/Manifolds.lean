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
import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds


noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsHypersurface (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y

def tangentSpace (ψ : E → ℝ) (y : E) : Submodule ℝ E :=
  LinearMap.ker (fderiv ℝ ψ y).toLinearMap

def IsRegularPoint (ψ : E → ℝ) (y : E) : Prop :=
  DifferentiableAt ℝ ψ y ∧ fderiv ℝ ψ y ≠ 0

end Hypersurface
end
