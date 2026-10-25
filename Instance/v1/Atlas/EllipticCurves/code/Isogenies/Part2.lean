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
import Theorem.v1.Atlas.EllipticCurves.code.Isogenies
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- The function field of a Weierstrass curve is a field. -/
noncomputable instance : Field W.FunctionField := inferInstance

/-- The function field of a Weierstrass curve is the fraction field of its
coordinate ring. -/
noncomputable instance : IsFractionRing W.CoordinateRing W.FunctionField := inferInstance

end WeierstrassCurve.Affine
