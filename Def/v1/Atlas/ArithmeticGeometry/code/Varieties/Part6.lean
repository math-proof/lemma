module
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Varieties.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable (k : Type*) [Field k]


/-- The Zariski topology on $\mathbb{A}^n_k$, whose closed sets are the algebraic sets. -/
@[reducible]
def zariskiTopology (n : ℕ) : TopologicalSpace (AffineSpace_k k n) :=
  TopologicalSpace.ofClosed (algebraicSetsCollection k n)
    (algebraicSetsCollection_empty_mem k n)
    (algebraicSetsCollection_sInter_mem k n)
    (algebraicSetsCollection_union_mem k n)

/-- Evaluate a tuple of polynomials at a point, giving a map $\mathbb{A}^m \to \mathbb{A}^n$. -/
def polyMapEval (m n : ℕ)
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  fun j => MvPolynomial.eval P (polys j)

