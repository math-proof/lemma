module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Analysis.Complex.Basic


public section

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
