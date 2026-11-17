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
public import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies.Part5
public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


/-- An isogeny `E₁ → E₂` between Weierstrass curves: a surjective group
homomorphism between their group-of-points along with a positive integer
"degree" attribute. (See Sutherland, definitions surrounding §5.1 — an isogeny
is a surjective morphism of elliptic curves that sends the identity to the
identity.) -/
structure Isogeny {F : Type u} [Field F] [DecidableEq F]
    (E₁ E₂ : WeierstrassCurve.Affine F) where
  toAddMonoidHom : E₁.Point →+ E₂.Point
  surjective : Function.Surjective toAddMonoidHom
  degree : ℕ
  degree_pos : 0 < degree

