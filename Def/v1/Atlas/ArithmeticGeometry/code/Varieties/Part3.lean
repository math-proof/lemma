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
import Instance.v1.Atlas.ArithmeticGeometry.code.Varieties
variable (k : Type*) [Field k]


/-- The function field $\bar{k}(V)$ is an algebra over the algebraic closure $\bar{k}$. -/
@[reducible] noncomputable def functionFieldBar.instAlgebra {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAffineVariety k n V) :
    Algebra (AlgebraicClosure k) (functionFieldBar k V hV) := by
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain k hV
  show Algebra (AlgebraicClosure k)
    (FractionRing (MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet V))
  infer_instance

