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

/-- The ring homomorphism that dehomogenizes a polynomial in three projective
variables by setting the third coordinate to `1`, sending `X₀ ↦ X`, `X₁ ↦ Y`,
`X₂ ↦ 1`. -/
noncomputable def dehomogenizeHom (k : Type u) [CommRing k] :
    MvPolynomial (Fin 3) k →+* k[X][Y] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C : k →+* k[X][Y])
    (![Polynomial.C Polynomial.X, Polynomial.X, 1])

/-- Dehomogenize a homogeneous polynomial in `MvPolynomial (Fin 3) k` to a bivariate
polynomial in `k[X][Y]` by substituting `Z = 1`. -/
noncomputable def dehomogenize (f : MvPolynomial (Fin 3) k) : k[X][Y] :=
  dehomogenizeHom k f

end ProjectiveCurve
