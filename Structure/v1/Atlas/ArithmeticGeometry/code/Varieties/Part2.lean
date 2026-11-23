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
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Varieties.Part4
public section

variable (k : Type*) [Field k]


/-- A rational map $X \dashrightarrow Y$ between affine varieties: a tuple of numerators/denominators, defined on an open dense subset of $X$, sending its domain into $Y$. -/
structure RationalMap (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) where
  nums : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)
  denoms_ne_zero : ∀ j, denoms j ≠ 0
  dom_open : IsOpenInVariety k m X (ratMapDom k m n X denoms)
  dom_dense : IsDenseInVariety k m X (ratMapDom k m n X denoms)
  maps_to : ∀ P ∈ ratMapDom k m n X denoms, ratMapEval k m n nums denoms P ∈ Y

