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
public import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- If the defining polynomial `f₀` of the curve is prime, then the coordinate ring
`k[X][Y]/(f₀)` is an integral domain. -/
noncomputable instance CoordinateRing.isDomain (f₀ : k[X][Y]) [hf : Fact (Prime f₀)] :
    IsDomain (CoordinateRing f₀) :=
  AdjoinRoot.isDomain_of_prime hf.out

/-- When `f₀` is prime, the function field of the curve is a genuine field, obtained
as the fraction field of the integral coordinate ring. -/
noncomputable instance FunctionField.instField (f₀ : k[X][Y]) [Fact (Prime f₀)] :
    Field (FunctionField f₀) :=
  inferInstance

end ProjectiveCurve
