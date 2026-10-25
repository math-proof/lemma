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
import Class.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part2
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- Assertion that the curvature matrix has every entry of homogeneous degree 2 (i.e., a 2-form). -/
def CurvatureMatrixDegreeTwo {r : ℕ} {R : Type*} [CommRing R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) : Prop :=
  ∀ i j, IsGradedFormAlgebra.IsHomog (curvMatrix i j) 2

/-- The $j$-th Chern class form $c_j$: the degree-$2j$ component of the total Chern form. -/
def chernClass {r : ℕ} {R : Type*} [CommRing R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) (j : ℕ) : R :=
  IsGradedFormAlgebra.proj (2 * j) (totalChernForm curvMatrix t)

/-- The total Chern form has no components of odd degree, since the curvature is a 2-form. -/
def ChernScalarHomogZero {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R] : Prop :=
  IsGradedFormAlgebra.IsHomog (algebraMap ℂ R chernScalar) 0

/-- Odd-degree components of the Chern form (with $\frac{i}{2\pi}$ normalization) vanish. -/
noncomputable def chernClassWithScalar {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R] [IsGradedFormAlgebra R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (j : ℕ) : R :=
  chernClass curvMatrix (algebraMap ℂ R chernScalar) j

/-- The first Chern form $c_1 = t \cdot \mathrm{tr}(\Omega)$, the linear-in-$t$ term of $\det(I + t\,\Omega)$. -/
def firstChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  t * curvMatrix.trace


/-- The top Chern form $c_r = t^r \det(\Omega)$, which on a compact oriented manifold equals the
Euler class $e(E) \in H^{2r}(M, \mathbb{Z})$. -/
def topChernForm {r : ℕ} {R : Type*} [CommRing R]
    (curvMatrix : Matrix (Fin r) (Fin r) R) (t : R) : R :=
  t ^ r * curvMatrix.det


