/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset BigOperators

namespace ProjectionTheory

/-- The finite range of dyadic exponents `{0, 1, …, ⌊log₂ R⌋}` used to index the scales
`r = 2^k` in dyadic decompositions up to a real cutoff `R`. -/
noncomputable def dyadicExponentRange (R : ℝ) : Finset ℕ :=
  Finset.range (Nat.log 2 ⌊R⌋₊ + 1)

/-- A point in the Euclidean plane `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Point2 := Fin 2 → ℝ

/-- A direction vector in `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Direction := Fin 2 → ℝ

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

/-- The data for the SETUP of the real-version double-counting theorem: a scale
parameter `R ≥ 1`, the cardinalities `|X|` and `|D|` of a planar point set and a
direction set, the maximal projection size `S` (with `0 < S ≤ |X|`), and the multiscale
covering numbers `N_X(r)`, `N_D(ρ)` at radii `r, ρ`. -/
structure DoubleCountingRealSetup where
  R : ℝ
  hR : 1 ≤ R
  cardX : ℕ
  cardD : ℕ
  S : ℕ
  hS_pos : 0 < S
  hS_le : S ≤ cardX
  N_X : ℝ → ℕ
  N_D : ℝ → ℕ
  hN_X_le : ∀ r, N_X r ≤ cardX
  hN_D_le : ∀ ρ, N_D ρ ≤ cardD

/-- The dyadic incidence-count sum `∑_{1 ≤ r ≤ R, dyadic} N_X(r) · N_D(1/r)` appearing
on the right-hand side of the real-version double-counting theorem. -/
noncomputable def dyadicSum (setup : DoubleCountingRealSetup) : ℕ :=
  ∑ k ∈ dyadicExponentRange setup.R, setup.N_X (2 ^ k) * setup.N_D ((2 : ℝ) ^ k)⁻¹
