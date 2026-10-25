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
import Instance.v1.Atlas.ArithmeticGeometry.code.Varieties.Part3
variable (k : Type*) [Field k]


/-- The dimension of an affine variety $V$ is the transcendence degree of its function field $\bar{k}(V)$ over $\bar{k}$ (Definition 12.21). -/
noncomputable def varietyDim {n : ℕ}
    (V : Set (AffineSpace_k k n)) (hV : IsAffineVariety k n V) : Cardinal :=
  Algebra.trdeg (AlgebraicClosure k) (functionFieldBar k V hV)

/-- A subset $V \subseteq \mathbb{A}^n$ is an algebraic set if it is the zero locus $\mathcal{V}(S)$ of some set $S$ of polynomials. -/
def IsAlgebraicSetAffine (n : ℕ) (V : Set (AffineSpace_k k n)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)), V = AlgebraicSet k n S

/-- The collection of all algebraic subsets of $\mathbb{A}^n$, used as the closed sets of the Zariski topology. -/
def algebraicSetsCollection (n : ℕ) : Set (Set (AffineSpace_k k n)) :=
  {V | IsAlgebraicSetAffine k n V}

