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
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part6
variable (k : Type*) [Field k]


/-- A morphism of affine varieties $X \to Y$ is given by an $n$-tuple of polynomials whose induced map sends $X$ into $Y$. -/
structure AffineMorphism (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  maps_to : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y

