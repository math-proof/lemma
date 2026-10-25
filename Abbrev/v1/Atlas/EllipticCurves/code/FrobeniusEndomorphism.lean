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
import Theorem.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism.Part2
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
