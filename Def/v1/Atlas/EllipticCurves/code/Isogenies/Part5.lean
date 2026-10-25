/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Inductive.v1.Atlas.EllipticCurves.code.Isogenies
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- Regularity of a rational map at a projective point: in the affine case use
`IsRegularAtOver`; at infinity, require that some scaling makes all coordinates
into a common ratio whose numerators are not all zero. -/
def RationalMap.IsRegularAtProjectivePoint {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : ProjectiveCurvePointOver f₁ K) : Prop :=
  match P with
  | .affine Q => φ.IsRegularAtOver Q
  | .atInfinity _a _b _hab =>
    ∃ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
      (∃ (μ : FunctionField f₁), μ ≠ 0 ∧
        μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h ∧
        μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h ∧
        μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h) ∧
      (g₁ ≠ 0 ∨ g₂ ≠ 0 ∨ g₃ ≠ 0)

/-- A rational map is a *morphism* if it is regular at every projective point of
the source curve over every algebraically closed extension. -/
def RationalMap.IsMorphism {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ P : ProjectiveCurvePointOver f₁ K,
      φ.IsRegularAtProjectivePoint P

end ProjectiveCurve
