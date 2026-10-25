/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part2
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

