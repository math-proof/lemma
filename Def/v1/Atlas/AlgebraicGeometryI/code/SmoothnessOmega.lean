/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessOmega.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.SmoothnessOmega


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
