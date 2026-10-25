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
import Def.v1.Atlas.EllipticCurves.code.Isogenies
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- The coordinate ring of the affine chart `{Z = 1}` of a projective plane curve
defined by a homogeneous polynomial `f ∈ k[X₀, X₁, X₂]`. -/
noncomputable abbrev CoordinateRingOfHomog (f : MvPolynomial (Fin 3) k) : Type u :=
  CoordinateRing (dehomogenize f)

/-- The function field of a projective plane curve obtained as the fraction field
of the affine coordinate ring of its `{Z = 1}` chart. -/
noncomputable abbrev FunctionFieldOfHomog (f : MvPolynomial (Fin 3) k) : Type u :=
  FunctionField (dehomogenize f)

end ProjectiveCurve
