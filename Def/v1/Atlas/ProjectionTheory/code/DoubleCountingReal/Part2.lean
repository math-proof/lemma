/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.ProjectionTheory.code.DoubleCountingReal
open Finset BigOperators


namespace ProjectionTheory

/-- The projection `π_θ(x) = x · θ = ∑_i x_i θ_i` of a planar point `x` onto the
direction `θ ∈ ℝ²`. -/
noncomputable def projDir (θ : Direction) (x : Point2) : ℝ :=
  ∑ i : Fin 2, x i * θ i

/-- The set of triples `(x₁, x₂, θ) ∈ X × X × D` whose projections under `θ` are within
distance `2`, i.e. `|π_θ(x₁) − π_θ(x₂)| ≤ 2`. Its cardinality is the incidence quantity
that is bounded both from below and above in the real-version double counting argument. -/
noncomputable def collisionSet (X : Finset Point2) (D : Finset Direction) :
    Finset (Point2 × Point2 × Direction) :=
  (X ×ˢ X ×ˢ D).filter fun ⟨x₁, x₂, θ⟩ =>
    |projDir θ x₁ - projDir θ x₂| ≤ 2

end ProjectionTheory
