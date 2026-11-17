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
public import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
public section

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

