/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplectomorphismFixedPoints.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part7
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.WeinsteinNeighborhood
set_option autoImplicit false


public noncomputable section

open Filter Topology


/-- A symplectic form on $M$: a smoothly varying nondegenerate skew-symmetric bilinear form $\omega_x : E \times E \to \mathbb{R}$ at each point. -/
structure SymplecticForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  form : M → E → E → ℝ
  bilinear_left : ∀ (x : M) (a b : ℝ) (v₁ v₂ w : E),
    form x (a • v₁ + b • v₂) w = a * form x v₁ w + b * form x v₂ w
  skewSymm : ∀ (x : M) (v w : E), form x v w = -(form x w v)
  nondegenerate : ∀ (x : M) (v : E), (∀ w : E, form x v w = 0) → v = 0

end
