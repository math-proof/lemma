/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ContinuumBeck.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProjectionTheory.code.DeltaRegular

open MeasureTheory Set Metric Classical DeltaRegular
open scoped ENNReal NNReal

noncomputable section

namespace ContinuumBeck

/-- Shorthand for the Euclidean plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/--
Predicate that `x` lies in the `ρ × 1` rectangle centered at `center`, oriented
along the unit vector `dir`: the projection of `x − center` onto `dir` has
absolute value at most `ρ/2`, and the projection onto the perpendicular
direction has absolute value at most `1/2`.
-/
def IsInRhoOneRectangle (center dir : E2) (ρ : ℝ) (x : E2) : Prop :=
  |∑ i, (x i - center i) * dir i| ≤ ρ / 2 ∧
  |(x 0 - center 0) * (- dir 1) + (x 1 - center 1) * dir 0| ≤ 1 / 2

/-- The `ρ × 1` rectangle in `ℝ²` centered at `center`, oriented along `dir`. -/
def RhoOneRectangle (center dir : E2) (ρ : ℝ) : Set E2 :=
  {x | IsInRhoOneRectangle center dir ρ x}

/--
The thin-rectangle hypothesis appearing in the Continuum Beck theorem: for
every `ρ × 1` rectangle `R` (any orientation), `|E ∩ R|_δ ≤ C ρ^η |E|_δ`.
-/
def RectangleCondition (δ η C : ℝ) (E : Set E2) : Prop :=
  ∀ center dir : E2, ‖dir‖ = 1 → ∀ ρ : ℝ, 0 < ρ →
    (deltaCoveringNumber δ (E ∩ RhoOneRectangle center dir ρ) : ℝ≥0∞) ≤
      ENNReal.ofReal (C * ρ ^ η) * (deltaCoveringNumber δ E : ℝ≥0∞)

/--
The set of unit-vector directions `(y − x)/‖y − x‖` for `y ∈ E \ {x}`. This
encodes the directions of lines through `x` that pass through another point of
`E`, as used in Beck's theorem.
-/
def directionsFromSet (x : E2) (E : Set E2) : Set E2 :=
  (fun y => (‖y - x‖⁻¹) • (y - x)) '' (E \ {x})

/--
Continuum Beck theorem (Orponen–Shmerkin–Wang, 2023). If `E ⊆ ℝ²` is a
`(δ, u, C)`-set satisfying the thin-rectangle condition (i.e.
`|E ∩ R|_δ ≤ C ρ^η |E|_δ` for every `ρ × 1` rectangle `R`), then for most
`x ∈ E` the set of directions `Lₓ,E = directionsFromSet x E` satisfies
`|Lₓ,E|_δ ≳ δ^ε · min(δ^{-u}, δ^{-1})`. The "most" is formalized as a
subset `E' ⊆ E` containing at least half of the `δ`-mass of `E`.
-/
end ContinuumBeck
