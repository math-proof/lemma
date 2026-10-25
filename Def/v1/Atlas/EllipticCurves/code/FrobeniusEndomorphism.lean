/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Theorem.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

variable [DecidableEq F]

/-- The induced self-map on the affine points $W(\overline{F})$ of a Weierstrass curve
given by an injective coefficient-fixing endomorphism: it fixes the point at infinity
and applies $\varphi$ coordinatewise to affine points. -/
noncomputable def pointMap (hφ : FixesCoeffs W φ)
    (hφ_inj : Function.Injective φ) : W.Point → W.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) (nonsingular_preserved hφ hφ_inj h)

end FrobeniusEndomorphism
