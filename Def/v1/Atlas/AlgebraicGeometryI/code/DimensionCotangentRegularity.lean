/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionCotangentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations

@[expose] public section

noncomputable section

open scoped TensorProduct

open KaehlerDifferential Algebra IsLocalRing Module

universe u v

section Goal135

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The module `Ω[A⁄k]` of Kähler differentials of the `k`-algebra `A`. -/
def kaehlerDifferentialsModule : Type _ := Ω[A⁄k]

/-- The universal property of `Ω[A⁄k]`: `A`-linear maps `Ω[A⁄k] → M` correspond naturally to
`k`-derivations `A → M`. -/
def goal136_universalProperty
    {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] :
    (Ω[A⁄k] →ₗ[A] M) ≃ₗ[A] Derivation k A M :=
  KaehlerDifferential.linearMapEquivDerivation k A

end Goal135
end
