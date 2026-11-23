/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part6
public section

variable (k : Type*) [Field k]


/-- A morphism of affine varieties $X \to Y$ is given by an $n$-tuple of polynomials whose induced map sends $X$ into $Y$. -/
structure AffineMorphism (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  maps_to : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y

