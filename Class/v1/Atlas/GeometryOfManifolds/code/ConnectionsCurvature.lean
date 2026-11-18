module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part2
public section
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace

/-- A ring $R$ equipped with a differential $d$ satisfying $d \circ d = 0$, abstracting the
exterior derivative on matrix-valued forms. -/
class MatrixFormAlgebra (R : Type*) extends Ring R where
  d : R → R
  d_add : ∀ a b, d (a + b) = d a + d b
  d_zero : d 0 = 0
  d_squared : ∀ a, d (d a) = 0

