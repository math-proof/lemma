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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.EllipticCurveSmooth
open Polynomial
open scoped Polynomial.Bivariate


namespace EllipticCurveSmooth

variable {k : Type*} [Field k]

/-- The coordinate ring `k[X][Y]/(Y² − X³ − aX − b)` of the affine Weierstrass
curve is an integral domain. -/
noncomputable instance weierstrass_coordinate_ring_isDomain (a b : k) :
    IsDomain (AdjoinRoot (weierstrass a b)) :=
  AdjoinRoot.isDomain_of_prime (Irreducible.prime (weierstrass_irreducible a b))

end EllipticCurveSmooth
