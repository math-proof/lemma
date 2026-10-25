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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part3
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

set_option synthInstance.maxHeartbeats 40000 in
/-- A rational map from the curve `f₁ = 0` to the curve `f₂ = 0`, represented by a
triple of elements `(φ₁ : φ₂ : φ₃)` in the function field of `f₁`, not all zero,
such that whenever `(φ₁ : φ₂ : φ₃)` is defined at a point with `φ₃ ≠ 0`, the image
lies on `f₂`. -/
structure RationalMap (f₁ f₂ : k[X][Y]) [IsDomain (CoordinateRing f₁)] where
  φ₁ : FunctionField f₁
  φ₂ : FunctionField f₁
  φ₃ : FunctionField f₁
  not_all_zero : φ₁ ≠ 0 ∨ φ₂ ≠ 0 ∨ φ₃ ≠ 0
  image_on_curve :
    ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
    ∀ (P : AffinePointOver f₁ K),
    ∀ (g₁ g₂ g₃ : CoordinateRing f₁)
      (h : ↥(nonZeroDivisors (CoordinateRing f₁))),
    φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h →
    φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h →
    φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h →
    P.evalRingHom (h : CoordinateRing f₁) ≠ 0 →
    (P.evalRingHom g₁ ≠ 0 ∨ P.evalRingHom g₂ ≠ 0 ∨ P.evalRingHom g₃ ≠ 0) →
    P.evalRingHom g₃ ≠ 0 →
    evalBivariate f₂ (P.evalRingHom g₁ / P.evalRingHom g₃)
      (P.evalRingHom g₂ / P.evalRingHom g₃) = 0

end ProjectiveCurve
