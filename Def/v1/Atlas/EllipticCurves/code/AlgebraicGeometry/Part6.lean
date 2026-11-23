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
public import Theorem.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part2

@[expose] public section

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
