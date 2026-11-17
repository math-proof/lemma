/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AlgebraicGeometryBasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.ENat
public import Theorem.v1.Atlas.ArithmeticGeometry.code.AlgebraicGeometryBasics
open Cardinal


@[expose] public noncomputable section

universe u v w w'

variable {ι : Type*}

/-- The transcendence degree of a field extension $L/k$: the cardinality of any transcendence basis. -/
abbrev transcendenceDegree (k L : Type*) [Field k] [Field L] [Algebra k L] : Cardinal :=
  Algebra.trdeg k L


end

open Order

/-- The Krull dimension of a commutative semiring: the supremum of lengths of chains of prime ideals. -/
noncomputable abbrev krullDimension (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  ringKrullDim R


