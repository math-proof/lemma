/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Theorem.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism.Part2
@[expose] public section

open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

variable [DecidableEq F]

/-- The base change of a Weierstrass curve $W/F$ along an algebra inclusion $F \hookrightarrow L$:
the same equation viewed over the larger field $L$. -/
noncomputable abbrev baseChange (W : WeierstrassCurve.Affine F) :
    WeierstrassCurve.Affine L :=
  W.map (algebraMap F L)

end FrobeniusEndomorphism
