/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Complex.Basic


noncomputable section

open scoped Manifold

open Bundle


/-- Typeclass wrapper recording that a vector bundle $V \to M$ has smooth transition functions (modeled in the DFS framework). -/
class SmoothVectorBundleDFS
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM]
    (I : ModelWithCorners ℝ EM HM)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*)
    [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
    [VectorBundle ℝ F V] : Prop where
  smoothTransitions : ContMDiffVectorBundle ⊤ F V I


end
