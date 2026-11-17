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
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part9

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ : WeierstrassCurve.Affine F}

open Polynomial

/-- Extract the affine coordinates `(x, y)` of a point of `E₁`, mapping the
identity to `none`. -/
noncomputable def pointToCoords : E₁.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

end Isogeny
end IsogenyStandardForm
