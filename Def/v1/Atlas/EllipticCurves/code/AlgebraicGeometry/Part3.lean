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
public import Abbrev.v1.Atlas.EllipticCurves.code.AlgebraicGeometry

@[expose] public section

open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- The canonical quotient map `K[x₁, …, xₙ] → K[V]` from the polynomial ring
to the coordinate ring of `V`. -/
def coordinateRing.mk (V : Set (σ → K)) :
    MvPolynomial σ K →+* coordinateRing K σ V :=
  Ideal.Quotient.mk _

end
