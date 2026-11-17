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
public import Class.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
public section

open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- The curvature tensor $R^\nabla: \mathfrak{X}(M) \times \mathfrak{X}(M) \to \mathrm{End}(E)$,
which is antisymmetric in its two vector-field arguments. -/
structure CurvatureTensor
    (Sections VectorFields EndSections : Type*)
    [AddCommGroup Sections] [AddCommGroup EndSections] where
  R : VectorFields → VectorFields → EndSections
  antisymm : ∀ U V, R U V = -(R V U)

