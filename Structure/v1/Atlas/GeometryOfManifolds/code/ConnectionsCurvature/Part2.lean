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
import Class.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
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

