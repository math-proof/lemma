/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part5

@[expose] public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- Construction of holomorphic frame data starting from a Hermitian metric, with connection
form $A = h^{-1} \partial h$. -/
def HolomorphicFrameData.mk_from_metric
    {R : Type*} [Ring R]
    (d del dbar : R → R) (h_inv del_h : R)

    (h_decomp : ∀ x, d x = del x + dbar x)

    (h_inv_deriv : del h_inv = -(h_inv * del_h * h_inv))

    (h_leib : del (h_inv * del_h) = del h_inv * del_h + h_inv * del del_h)

    (h_del_sq : del del_h = 0) :
    HolomorphicFrameData R where
  A := h_inv * del_h
  d := d
  del := del
  dbar := dbar
  d_eq_del_add_dbar := h_decomp
  del_A_eq := by

    rw [h_leib, h_del_sq, mul_zero, add_zero, h_inv_deriv]
    noncomm_ring

/-- Opaque predicate stating that a vector bundle admits a holomorphic structure. -/
opaque IsHolomorphicBundle : Type* → Prop

/-- Opaque predicate stating that $\bar\partial_\nabla^2 = 0$ for the $(0,1)$-part of $\nabla$. -/
opaque DbarNablaSqZero : Type* → Prop

/-- Opaque predicate stating that the $(0,2)$-part of the curvature vanishes. -/
opaque CurvR02Vanishes : Type* → Prop


