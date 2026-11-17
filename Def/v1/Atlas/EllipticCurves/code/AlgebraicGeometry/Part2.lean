/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Theorem.v1.Atlas.EllipticCurves.code.AlgebraicGeometry

@[expose] public section

open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- An algebraic set is irreducible if it is nonempty and cannot be written
as the union of two strictly smaller algebraic sets. This is Definition 4.54. -/
def IsIrreducibleAffineAlgebraicSet (K : Type*) [Field K]
    (V : Set (σ → K)) : Prop :=
  IsAffineAlgebraicSet K V ∧
  V.Nonempty ∧
  ∀ V₁ V₂ : Set (σ → K),
    IsAffineAlgebraicSet K V₁ →
    IsAffineAlgebraicSet K V₂ →
    V = V₁ ∪ V₂ → V = V₁ ∨ V = V₂

/-- An affine variety is an irreducible affine algebraic set. -/
def IsAffineVariety (K : Type*) [Field K] (V : Set (σ → K)) : Prop :=
  IsIrreducibleAffineAlgebraicSet K V

/-- The vanishing ideal `I(V)` of a set of points: all polynomials that
vanish identically on `V`. This is Definition 4.46. -/
def vanishingIdealOfSet (K : Type*) [Field K]
    (V : Set (σ → K)) : Ideal (MvPolynomial σ K) :=
  MvPolynomial.vanishingIdeal K V

end
