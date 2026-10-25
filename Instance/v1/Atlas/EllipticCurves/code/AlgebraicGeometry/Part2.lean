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
import Abbrev.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part2
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
