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
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- The trivial zero connection on $\mathbb{R}$, serving as a base example. -/
noncomputable def Connection.trivial : Connection ℝ ℝ ℝ (fun _ _ => 0) where
  nabla := fun _ => 0
  nabla_add := by simp
  nabla_smul_real := by simp
  leibniz := by simp [smul_eq_mul]

/-- The space of connections is an affine space: adding an $\mathrm{End}(E)$-valued one-form $B$
to a connection $\nabla$ gives a new connection $\nabla + B$. -/
def Connection.add
    {Sections FormsWithValues Functions : Type*}
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    {dfSmul : Functions → Sections → FormsWithValues}
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (B : Sections → FormsWithValues)
    (B_add : ∀ σ τ, B (σ + τ) = B σ + B τ)
    (B_smul_real : ∀ (c : ℝ) (σ : Sections), B (c • σ) = c • B σ)
    (B_linear : ∀ (f : Functions) (σ : Sections), B (f • σ) = f • B σ) :
    Connection Sections FormsWithValues Functions dfSmul where
  nabla := fun σ => conn.nabla σ + B σ
  nabla_add := by intro σ τ; rw [conn.nabla_add, B_add]; abel
  nabla_smul_real := by intro c σ; rw [conn.nabla_smul_real, B_smul_real, smul_add]
  leibniz := by
    intro f σ
    simp only [conn.leibniz, B_linear]
    rw [smul_add]
    abel

/-- The covariant derivative $\nabla_v \sigma$ of a section $\sigma$ along a vector field $v$,
obtained by evaluating $\nabla\sigma \in \Omega^1(M, E)$ on $v$. -/
def Connection.covariantDeriv
    {Sections FormsWithValues Functions VectorFields : Type*}
    [AddCommGroup Sections] [Module ℝ Sections]
    [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
    [Ring Functions] [Module Functions Sections] [Module Functions FormsWithValues]
    {dfSmul : Functions → Sections → FormsWithValues}
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (eval : VectorFields → FormsWithValues → Sections)
    (v : VectorFields) (σ : Sections) : Sections :=
  eval v (conn.nabla σ)

section MetricCompatibility

variable {Sections FormsWithValues Functions OneForm : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup FormsWithValues] [Module ℝ FormsWithValues]
  [Ring Functions] [AddCommGroup OneForm]
  [Module Functions Sections] [Module Functions FormsWithValues]
  {dfSmul : Functions → Sections → FormsWithValues}

/-- A connection $\nabla$ is metric-compatible with a metric $\langle\cdot,\cdot\rangle$ iff
$d\langle \sigma, \sigma'\rangle = \langle \nabla\sigma, \sigma'\rangle + \langle \sigma, \nabla\sigma'\rangle$. -/
def MetricCompatible
    (conn : Connection Sections FormsWithValues Functions dfSmul)
    (metric : Sections → Sections → Functions)
    (dFunctions : Functions → OneForm)
    (pairNablaLeft : FormsWithValues → Sections → OneForm)
    (pairNablaRight : Sections → FormsWithValues → OneForm) : Prop :=
  ∀ σ σ',
    dFunctions (metric σ σ') =
      pairNablaLeft (conn.nabla σ) σ' + pairNablaRight σ (conn.nabla σ')

end MetricCompatibility
