module
public import Def.v1.Atlas.LieGroups.code.Admissible.Part3
public import Theorem.LinearMap.EqContinuousLinearEquivOfBijective.of.Bijective
public import Theorem.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
public import Theorem.Complex.IsKFinite0
public import Def.v1.Atlas.LieGroups.code.SmoothVectors
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Structure.v1.Atlas.LieGroups.code.AnalyticityRegularity


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe uLie


noncomputable section

open scoped Manifold

namespace ContinuousRep

section WeaklyAnalytic

universe uFsec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H)

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]

variable [LieGroup I ⊤ G]

variable {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]

noncomputable def restrictEndomorphism (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) : W →ₗ[ℂ] W :=
  b.restrict hb

end WeaklyAnalytic
end ContinuousRep
end
