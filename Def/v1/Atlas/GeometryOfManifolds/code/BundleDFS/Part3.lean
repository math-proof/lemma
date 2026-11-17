/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Analysis.Complex.Basic
public import Structure.v1.Atlas.GeometryOfManifolds.code.BundleDFS

@[expose] public section

noncomputable section

open scoped Manifold

open Bundle


namespace ConnectionDFS

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

/-- Apply a connection: $(\nabla_X \sigma)_x = \mathtt{conn.apply}\ \sigma\ x\ X$. -/
def apply (conn : ConnectionDFS I M F V) (σ : ∀ x : M, V x) (x : M)
    (X : TangentSpace I x) : V x :=
  conn.nabla σ x X

/-- The difference $\nabla_1 - \nabla_2$ of two connections (an $\mathrm{End}(V)$-valued $1$-form). -/
def difference (conn₁ conn₂ : ConnectionDFS I M F V) :
    (∀ x : M, V x) → (∀ x : M, TangentSpace I x →L[ℝ] V x) :=
  fun σ x => conn₁.nabla σ x - conn₂.nabla σ x

end ConnectionDFS
end
