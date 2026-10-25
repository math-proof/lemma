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
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties
variable (k : Type*) [Field k]


/-- The coordinate ring $\bar{k}[V]$ of an affine variety $V$ is an integral domain. -/
theorem coordinateRingBar_isDomain {n : ℕ} {V : Set (AffineSpace_k k n)}
    (hV : IsAffineVariety k n V) :
    IsDomain (AffineCoordinateRingBar V) := by
  have hprime := (isIrreducibleAlgebraicSet_iff_isPrime k hV.1).mp hV.2
  exact Ideal.Quotient.isDomain (idealOfAlgebraicSet V)

