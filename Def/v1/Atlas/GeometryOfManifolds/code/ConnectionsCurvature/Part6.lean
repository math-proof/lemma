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
public import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part4

@[expose] public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- A representative of the first Chern class of a line bundle: $c_1(L) = [\frac{1}{2\pi} R^\nabla]$. -/
noncomputable def firstChernClassRep
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (curvature : Ω 2) : Ω 2 :=
  (1 / (2 * Real.pi)) • curvature

/-- The first Chern class representative of a line bundle connection: $\frac{1}{2\pi} R^\nabla$. -/
noncomputable def firstChernClassOfLineBundle
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    (conn : LineBundleConnection Ω VF) : Ω 2 :=
  firstChernClassRep (VF := VF) conn.curvature


