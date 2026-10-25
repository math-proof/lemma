/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Theorem.v1.Atlas.EllipticCurves.code.AlgebraicGeometry
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
