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
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- Evaluation ring homomorphism from the coordinate ring `k[X][Y]/(f₀)` to `L`
induced by a point `P = (x, y)` of the curve over `L`. -/
noncomputable def AffinePointOver.evalRingHom {f₀ : k[X][Y]} {L : Type v}
    [CommRing L] [Algebra k L]
    (P : AffinePointOver f₀ L) : CoordinateRing f₀ →+* L :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (algebraMap k L) P.x) P.y P.on_curve

end ProjectiveCurve
