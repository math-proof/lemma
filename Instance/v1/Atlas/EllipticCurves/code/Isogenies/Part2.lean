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
public import Theorem.v1.Atlas.EllipticCurves.code.Isogenies

@[expose] public section

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
