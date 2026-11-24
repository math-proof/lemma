module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable (k : Type*) [Field k]


/-- The coordinate ring $\bar{k}[V]$ of an affine variety $V$ is an integral domain. -/
theorem coordinateRingBar_isDomain {n : ℕ} {V : Set (AffineSpace_k k n)}
    (hV : IsAffineVariety k n V) :
    IsDomain (AffineCoordinateRingBar V) := by
  have hprime := (isIrreducibleAlgebraicSet_iff_isPrime k hV.1).mp hV.2
  exact Ideal.Quotient.isDomain (idealOfAlgebraicSet V)

