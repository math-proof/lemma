/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.DimensionTheory
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DimensionTheory
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.DiscreteValuationRing.Basic


noncomputable section

open Ideal

/-- Serre's dimension inequality: for a Noetherian local ring `R` and primes `𝔭`, `𝔮`,
`dim(R/𝔭) + dim(R/𝔮) ≤ dim R + dim(R/(𝔭 ⊔ 𝔮))`. -/
class HasSerreDimensionInequality (R : Type*) [CommRing R] [IsLocalRing R] : Prop where
  dim_ineq : ∀ {𝔭 𝔮 : Ideal R} [𝔭.IsPrime] [𝔮.IsPrime],
    ringKrullDim (R ⧸ 𝔭) + ringKrullDim (R ⧸ 𝔮) ≤
      ringKrullDim R + ringKrullDim (R ⧸ (𝔭 ⊔ 𝔮))

end
