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
import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- A vector bundle admits a holomorphic structure iff $\bar\partial_\nabla^2 = 0$. -/
structure HolomorphicVectorBundle
    (BundleValuedForms : ℕ → Type*) [∀ q, AddCommGroup (BundleValuedForms q)] where
  dbar_E : ∀ {q : ℕ}, BundleValuedForms q → BundleValuedForms (q + 1)
  dbar_add : ∀ {q : ℕ} (σ τ : BundleValuedForms q),
    dbar_E (σ + τ) = dbar_E σ + dbar_E τ
  dbar_squared : ∀ {q : ℕ} (σ : BundleValuedForms q), dbar_E (dbar_E σ) = 0

/-- A $\bar\partial_E$-closed form of bidegree $(0,q)$ with values in $E$, representing a
Dolbeault cohomology class in $H^{0,q}(M, E)$. -/
structure DolbeaultCohomologyWithCoefficients
    {BundleValuedForms : ℕ → Type*} [∀ q, AddCommGroup (BundleValuedForms q)]
    (E : HolomorphicVectorBundle BundleValuedForms)
    (q : ℕ) where
  representative : BundleValuedForms q
  is_closed : E.dbar_E representative = 0

