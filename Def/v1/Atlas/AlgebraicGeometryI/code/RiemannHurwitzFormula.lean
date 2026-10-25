/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Discriminant
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4


noncomputable section

open Ideal Module

namespace RiemannHurwitzFormula

section DVRRamification

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

variable [Algebra R S]

/-- The ramification index of an extension of DVRs `R ⊆ S`, defined as the
ramification index of the maximal ideals. -/
def DVRRamificationIndex : ℕ :=
  (IsLocalRing.maximalIdeal R).ramificationIdx (IsLocalRing.maximalIdeal S)

/-- An extension of DVRs `R ⊆ S` is unramified iff the ramification index equals 1. -/
def DVRIsUnramified : Prop :=
  DVRRamificationIndex (R := R) (S := S) = 1

/-- The local degree at `p` of the ramification divisor of an extension
`R ⊆ S` of Dedekind domains: the sum over primes `P` over `p` of `e_P - 1`. -/
def ramificationDivisorDegreeAt
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

end DVRRamification
end RiemannHurwitzFormula
end
