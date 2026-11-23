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
public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds

@[expose] public section

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
