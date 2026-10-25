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
import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- If the defining polynomial `f₀` of the curve is prime, then the coordinate ring
`k[X][Y]/(f₀)` is an integral domain. -/
noncomputable instance CoordinateRing.isDomain (f₀ : k[X][Y]) (hf : Prime f₀) :
    IsDomain (CoordinateRing f₀) :=
  AdjoinRoot.isDomain_of_prime hf

/-- When `f₀` is prime, the function field of the curve is a genuine field, obtained
as the fraction field of the integral coordinate ring. -/
noncomputable instance FunctionField.instField (f₀ : k[X][Y]) [h : Fact (Prime f₀)] :
    Field (FunctionField f₀) := by
  letI : IsDomain (CoordinateRing f₀) := CoordinateRing.isDomain f₀ h.out
  exact inferInstance

end ProjectiveCurve
