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
public import Abbrev.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part2
@[expose] public section

open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- When `I(V)` is prime, the coordinate ring `K[V]` is an integral domain. -/
instance coordinateRing.isDomain_of_prime (V : Set (σ → K))
    [(vanishingIdealOfSet K V).IsPrime] :
    IsDomain (coordinateRing K σ V) :=
  Ideal.Quotient.isDomain _

/-- When `I(V)` is prime, the affine function field of `V` is genuinely a
field (it is the fraction field of an integral domain). -/
instance affineFunctionField.field_of_prime (V : Set (σ → K))
    [(vanishingIdealOfSet K V).IsPrime] :
    Field (affineFunctionField K σ V) :=
  FractionRing.field _

end
