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
open Bundle NormedSpace
open scoped Manifold ContDiff Topology


/-- Generating polynomial for Chern forms: $\det(I + t\,\Omega)$ where $\Omega$ is the
curvature matrix. -/
def ChernForm
    {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  (1 + t • curvMatrix).det


