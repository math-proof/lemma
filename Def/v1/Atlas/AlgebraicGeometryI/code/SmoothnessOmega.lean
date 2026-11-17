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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.SmoothnessOmega

@[expose] public section

noncomputable section

open KaehlerDifferential Algebra

universe u v

section EmbeddingDimension

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **Regular local ring**: Krull dimension equals embedding dimension. -/
def IsRegularLocal : Prop :=
  ringKrullDim R = ↑(embDim R)

end EmbeddingDimension
end
