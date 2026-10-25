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
import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- A connection $\nabla: C^\infty(M, E) \to \Omega^1(M, E)$ on a vector bundle: an $\mathbb{R}$-linear
map satisfying the Leibniz rule $\nabla(f\sigma) = df \cdot \sigma + f \nabla \sigma$. -/
structure Connection (Sections FormsWithValues Functions : Type*)
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    (dfSmul : Functions → Sections → FormsWithValues) where
  nabla : Sections → FormsWithValues
  nabla_add : ∀ σ τ, nabla (σ + τ) = nabla σ + nabla τ
  nabla_smul_real : ∀ (c : ℝ) (σ : Sections), nabla (c • σ) = c • nabla σ
  leibniz : ∀ (f : Functions) (σ : Sections),
    nabla (f • σ) = dfSmul f σ + f • nabla σ

