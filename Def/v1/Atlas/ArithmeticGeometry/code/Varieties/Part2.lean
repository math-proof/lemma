/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Theorem.v1.Atlas.ArithmeticGeometry.code.Varieties
variable (k : Type*) [Field k]


/-- The function field $\bar{k}(V)$ of an affine variety, defined as the fraction field of the coordinate ring $\bar{k}[V]$. -/
noncomputable def functionFieldBar {n : ℕ}
    (V : Set (AffineSpace_k k n)) (hV : IsAffineVariety k n V) : Type _ :=
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  FractionRing (AffineCoordinateRingBar V)

/-- The function field $\bar{k}(V)$ is a field. -/
@[reducible] noncomputable def functionFieldBar.instField {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAffineVariety k n V) :
    Field (functionFieldBar k V hV) := by
  unfold functionFieldBar
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  exact FractionRing.field (AffineCoordinateRingBar V)

