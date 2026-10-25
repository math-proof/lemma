/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz.Part3
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- A bundling of the affine variety condition: `A` is a finite-type `k`-algebra and `Spec A`
represents the functor `X ↦ Hom_{Ring}(A, Γ(X, 𝒪_X))`. -/
structure IsAffineVariety' (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A] : Prop where
  finiteType : Algebra.FiniteType k A
  yoneda_bijective : ∀ (X : Scheme), Function.Bijective (yonedaPullback (CommRingCat.of A) X)

end
end Lec1ZariskiNullstellensatz
