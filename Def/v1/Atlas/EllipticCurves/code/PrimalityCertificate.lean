/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Pow.Real


namespace ECPrimality

/-- The short Weierstrass curve $y^2 = x^3 + Ax + B$ over a commutative ring $R$. -/
def shortWeierstrass (R : Type*) [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, A, B⟩

/-- The affine short Weierstrass curve $y^2 = x^3 + Ax + B$ reduced modulo $n$. -/
def curveModN (n : ℕ) (A B : ℤ) : WeierstrassCurve.Affine (ZMod n) :=
  (shortWeierstrass (ZMod n) (↑A) (↑B)).toAffine

end ECPrimality
