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
public import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part3

@[expose] public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- The total Chern form of a connection, computed from its curvature matrix via the
$\frac{i}{2\pi}$-normalized $\det(I + \cdot)$ formula. -/
noncomputable def chernFormOfConnection
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [∀ x : M, TopologicalSpace (V x)]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [FiberBundle F V]
    {r : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]
    (data : VectorBundleChernData 𝕜 E H I M F V r R) : R :=
  totalChernFormWithScalar data.curvatureMatrix

