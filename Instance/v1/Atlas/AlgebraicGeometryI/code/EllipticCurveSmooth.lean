/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.EllipticCurveSmooth

@[expose] public section

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
