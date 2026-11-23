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
public import Instance.v1.Atlas.AlgebraicGeometryI.code.EllipticCurveSmooth

@[expose] public section

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
