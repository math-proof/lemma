/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth


@[expose] public noncomputable section

open KaehlerDifferential Algebra

universe u v

section EmbeddingDimension

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **Embedding dimension** of a Noetherian local ring `R`: the minimal number
of generators of the maximal ideal, equivalently `dim_κ(𝔪/𝔪²)`. -/
abbrev embDim : ℕ := Submodule.spanFinrank (IsLocalRing.maximalIdeal R)

end EmbeddingDimension
end
