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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies
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
