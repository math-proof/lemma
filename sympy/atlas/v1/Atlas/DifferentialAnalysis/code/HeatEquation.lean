/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped SchwartzMap
open TemperedDistribution LineDeriv

namespace DifferentialOperators

variable (n : ℕ)

/-- The `(n + 1)`-dimensional spacetime `ℝ^{1+n}`, with the first coordinate
playing the role of time and the remaining `n` coordinates the spatial ones. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

/-- The unit vector in the time direction of `SpaceTime n`. -/
def timeDirection : SpaceTime n :=
  EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)

/-- The unit vector in the `i`-th spatial direction of `SpaceTime n`. -/
def spatialDirection (i : Fin n) : SpaceTime n :=
  EuclideanSpace.single i.succ (1 : ℝ)

/-- The positive spatial Laplacian acting on tempered distributions on
`SpaceTime n`: `Σᵢ ∂ᵢ²` summed over the spatial directions. -/
def positiveSpatialLaplacian (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∑ i : Fin n, ∂_{spatialDirection n i} (∂_{spatialDirection n i} u)

/-- The heat operator `∂ₜ − Δ` on tempered distributions on `SpaceTime n`. -/
def heatOperator (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∂_{timeDirection n} u - positiveSpatialLaplacian n u

/-- A tempered distribution `u` vanishes on an open set `U` if it pairs to
zero with every Schwartz function whose support is contained in `U`. -/
def DistributionVanishesOn (u : 𝓢'(SpaceTime n, ℂ)) (U : Set (SpaceTime n)) : Prop :=
  ∀ φ : 𝓢(SpaceTime n, ℂ), tsupport (⇑φ) ⊆ U → u φ = 0

/-- The distributional support of `u`: the set of points without any open
neighbourhood on which `u` vanishes (i.e., the complement of the largest
open set on which `u` vanishes). -/
def distributionalSupport (u : 𝓢'(SpaceTime n, ℂ)) : Set (SpaceTime n) :=
  {x | ¬∃ U : Set (SpaceTime n), IsOpen U ∧ x ∈ U ∧ DistributionVanishesOn n u U}

/-- A tempered distribution has compact distributional support iff its
distributional support is a compact set. -/
def HasCompactDistributionalSupport (u : 𝓢'(SpaceTime n, ℂ)) : Prop :=
  IsCompact (distributionalSupport n u)

/-- The time coordinate (first component) of a point in `SpaceTime n`. -/
def timeCoord (x : SpaceTime n) : ℝ := x 0

/-- A tempered distribution `u` is supported in the half-space `{t ≥ c}` if
its distributional support lies in `{x | timeCoord x ≥ c}`. -/
def SupportedInTimeGeq (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) : Prop :=
  distributionalSupport n u ⊆ {x : SpaceTime n | timeCoord n x ≥ c}
