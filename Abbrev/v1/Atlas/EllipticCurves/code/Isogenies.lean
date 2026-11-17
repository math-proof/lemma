/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Squarefree.Basic
@[expose] public section

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
