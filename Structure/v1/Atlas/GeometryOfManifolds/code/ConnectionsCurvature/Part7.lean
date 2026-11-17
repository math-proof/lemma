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
public import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part8
public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- The Chern connection on a Hermitian holomorphic bundle: the unique connection compatible
with the Hermitian metric $h$ whose $(0,1)$-part is $\bar\partial$, with connection form
$A = h^{-1} \partial h$. -/
structure ChernConnection (R : Type*) [Ring R] where
  del : R → R
  dbar : R → R
  d : R → R
  h : R
  h_inv : R
  h_inv_left : h_inv * h = 1
  h_inv_right : h * h_inv = 1
  d_decomp : ∀ x, d x = del x + dbar x
  A : R
  A_eq : A = h_inv * del h
  metric_compat : h * A = del h

