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
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part5

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

/-- The degree of an isogeny in standard form: `deg α := max (deg u) (deg v)`
(see Definition for Theorem 5.22 / standard-form degree). -/
noncomputable def degree (α : IsogenyStandardForm F) : ℕ :=
  max α.u.natDegree α.v.natDegree

/-- An isogeny in standard form is *separable* if `u'v - uv' ≠ 0`. -/
def IsSeparable (α : IsogenyStandardForm F) : Prop :=
  Polynomial.derivative α.u * α.v - α.u * Polynomial.derivative α.v ≠ 0

/-- An isogeny is *inseparable* if it is not separable. -/
def IsInseparable (α : IsogenyStandardForm F) : Prop :=
  ¬ α.IsSeparable

end IsogenyStandardForm
