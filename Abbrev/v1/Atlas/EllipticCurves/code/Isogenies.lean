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
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- The (affine) coordinate ring of a plane curve cut out by a bivariate polynomial
`f₀ ∈ k[X][Y]`, defined as the quotient `k[X][Y]/(f₀)` via `AdjoinRoot`. -/
noncomputable abbrev CoordinateRing (f₀ : k[X][Y]) : Type u :=
  AdjoinRoot f₀

/-- The function field of a plane curve, defined as the field of fractions of its
coordinate ring `k[X][Y]/(f₀)`. -/
noncomputable abbrev FunctionField (f₀ : k[X][Y]) : Type u :=
  FractionRing (CoordinateRing f₀)

end ProjectiveCurve
