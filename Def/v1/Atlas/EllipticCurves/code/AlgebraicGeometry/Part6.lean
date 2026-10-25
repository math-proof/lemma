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
import Theorem.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part2
open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- The Zariski topology on `σ → K`: closed sets are exactly the affine
algebraic sets, with closure under empty, arbitrary intersection, and
finite unions. -/
@[reducible]
def zariskiTopology (K : Type*) [Field K] (σ : Type*) : TopologicalSpace (σ → K) :=
  TopologicalSpace.ofClosed
    {V : Set (σ → K) | IsAffineAlgebraicSet K V}
    isAffineAlgebraicSet_empty
    (fun _ hA => isAffineAlgebraicSet_sInter _ hA)
    (fun _ h₁ _ h₂ => isAffineAlgebraicSet_union h₁ h₂)

/-- Predicate saying that an algebraic set consists of a single point. -/
def IsPoint (K : Type*) [Field K] (V : Set (σ → K)) : Prop :=
  ∃ P : σ → K, V = {P}

end
