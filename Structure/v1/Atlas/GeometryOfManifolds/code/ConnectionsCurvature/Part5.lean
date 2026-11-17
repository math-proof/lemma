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
public import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part6
public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- Data for the Chern connection in a holomorphic frame: a connection form $A$ with the
decomposition $d = \partial + \bar\partial$ and the identity $\partial A = -A \wedge A$. -/
structure HolomorphicFrameData (R : Type*) [Ring R] where
  A : R
  d : R → R
  del : R → R
  dbar : R → R
  d_eq_del_add_dbar : ∀ x, d x = del x + dbar x
  del_A_eq : del A = -(A * A)

