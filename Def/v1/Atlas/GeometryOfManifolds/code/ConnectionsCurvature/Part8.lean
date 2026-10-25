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
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part6
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- Cohomological equivalence: two $(0,q+1)$-forms represent the same Dolbeault class iff their
difference is $\bar\partial_E$-exact. -/
def DolbeaultCohomologyWithCoefficients.Equiv
    {BundleValuedForms : ℕ → Type*} [∀ q, AddCommGroup (BundleValuedForms q)]
    {E : HolomorphicVectorBundle BundleValuedForms}
    {q : ℕ}
    (c₁ c₂ : DolbeaultCohomologyWithCoefficients E (q + 1)) : Prop :=
  ∃ (β : BundleValuedForms q), c₁.representative - c₂.representative = E.dbar_E β

