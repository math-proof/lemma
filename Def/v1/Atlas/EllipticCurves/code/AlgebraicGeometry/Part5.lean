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
import Instance.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part2
open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- The canonical embedding of the coordinate ring `K[V]` into its fraction
field, the affine function field of `V`. -/
def affineFunctionField.ofCoordinateRing (V : Set (σ → K)) :
    coordinateRing K σ V →+* affineFunctionField K σ V :=
  algebraMap _ _

/-- The dimension of an affine variety `V` over `k`: the transcendence degree
over `k` of its affine function field. This realizes Definition 4.35
specialized to affine varieties. -/
noncomputable def varietyDimension (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K]
    (σ : Type*) (V : Set (σ → K)) [(vanishingIdealOfSet K V).IsPrime] : Cardinal :=
  Algebra.trdeg k (affineFunctionField K σ V)

end
