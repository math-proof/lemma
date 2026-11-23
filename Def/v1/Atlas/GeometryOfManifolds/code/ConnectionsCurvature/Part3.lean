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
public import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part2

@[expose] public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- The Chern normalization constant $\frac{i}{2\pi}$ appearing in $c(E,\nabla) = \det(I + \frac{i}{2\pi} R^\nabla)$. -/
noncomputable def chernScalar : ℂ := Complex.I / (2 * ↑Real.pi)

/-- The total Chern form generating polynomial: $\det(I + t\,\Omega)$ for a curvature matrix $\Omega$. -/
def totalChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  (1 + t • curvMatrix).det

/-- The total Chern form $c(E,\nabla) = \det(I + \frac{i}{2\pi} R^\nabla)$, using the standard
normalization constant $\frac{i}{2\pi}$. -/
noncomputable def totalChernFormWithScalar {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) : R :=
  totalChernForm curvMatrix (algebraMap ℂ R chernScalar)

