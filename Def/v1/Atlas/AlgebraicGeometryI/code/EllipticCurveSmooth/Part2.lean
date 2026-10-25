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
import Instance.v1.Atlas.AlgebraicGeometryI.code.EllipticCurveSmooth
open Polynomial
open scoped Polynomial.Bivariate


namespace EllipticCurveSmooth

variable {k : Type*} [Field k]

/-- Ring equivalence between our coordinate ring and the mathlib affine
coordinate ring, transporting via `weierstrass_eq_polynomial`. -/
noncomputable def coordinateRingEquiv (a b : k) :
    AdjoinRoot (weierstrass a b) ≃+*
      AdjoinRoot (shortWeierstrass a b).toAffine.polynomial :=
  RingEquiv.cast (by rw [weierstrass_eq_polynomial])

end EllipticCurveSmooth
