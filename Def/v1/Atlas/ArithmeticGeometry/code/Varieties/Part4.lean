module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Instance.v1.Atlas.ArithmeticGeometry.code.Varieties.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable (k : Type*) [Field k]


/-- The $k$-rational function field $k(V)$ of an affine variety, defined as the fraction field of the $k$-coordinate ring $k[V]$ when it is a domain. -/
noncomputable def functionField_k {n : ℕ}
    (V : Set (AffineSpace_k k n)) (_hV : IsAffineVariety k n V)
    (_hdom : IsDomain (AffineCoordinateRing V)) : Type _ :=
  FractionRing (AffineCoordinateRing V)

