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
import Theorem.v1.Atlas.ArithmeticGeometry.code.Varieties.Part3
variable (k : Type*) [Field k]


/-- A subset $U$ of a variety $X$ is open in $X$ iff $U = X \cap W$ for some Zariski-open $W$. -/
def IsOpenInVariety (m : ℕ) (X U : Set (AffineSpace_k k m)) : Prop :=
  U ⊆ X ∧ ∃ W : Set (AffineSpace_k k m), @IsOpen _ (zariskiTopology k m) W ∧ U = X ∩ W

/-- A subset $U$ is dense in the variety $X$ iff $X$ is contained in the Zariski closure of $U$. -/
def IsDenseInVariety (m : ℕ) (X U : Set (AffineSpace_k k m)) : Prop :=
  X ⊆ @closure _ (zariskiTopology k m) U

/-- Evaluate a rational function $\mathrm{num}/\mathrm{denom}$ at a point $P$. -/
def ratFunEval (m : ℕ)
    (num denom : MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AlgebraicClosure k :=
  MvPolynomial.eval P num / MvPolynomial.eval P denom

/-- Evaluate a rational map $\mathbb{A}^m \dashrightarrow \mathbb{A}^n$ given by tuples of numerators and denominators. -/
def ratMapEval (m n : ℕ)
    (nums denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) : AffineSpace_k k n :=
  fun j => ratFunEval k m (nums j) (denoms j) P

/-- The domain of definition of a rational map: points of $X$ where every denominator is nonzero. -/
def ratMapDom (m n : ℕ)
    (X : Set (AffineSpace_k k m))
    (denoms : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)) : Set (AffineSpace_k k m) :=
  {P ∈ X | ∀ j, MvPolynomial.eval P (denoms j) ≠ 0}

