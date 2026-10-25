/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
open Polynomial
open scoped Polynomial.Bivariate


namespace EllipticCurveSmooth

variable {k : Type*} [Field k]

/-- The short Weierstrass curve `y² = x³ + a x + b` packaged as a `WeierstrassCurve`. -/
noncomputable def shortWeierstrass (a b : k) : WeierstrassCurve k where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

/-- The bivariate Weierstrass polynomial `Y² − (X³ + aX + b)`, viewed in `k[X][Y]`. -/
noncomputable def weierstrass (a b : k) : Polynomial (Polynomial k) :=
  Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b)

end EllipticCurveSmooth
