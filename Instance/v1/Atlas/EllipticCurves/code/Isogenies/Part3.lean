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
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part6

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ E₃ : WeierstrassCurve.Affine F}

/-- An isogeny may be applied to points like a function. -/
instance : CoeFun (Isogeny E₁ E₂) (fun _ => E₁.Point → E₂.Point) where
  coe φ := φ.toAddMonoidHom

end Isogeny
