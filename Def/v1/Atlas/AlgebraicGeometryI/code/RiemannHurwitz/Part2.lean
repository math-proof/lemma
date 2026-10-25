/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Algebraic.Integral
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Instance.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz


noncomputable section

open Ideal Module

section RamificationDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]

/-- Local contribution at `p` to the ramification divisor: the sum
`∑_{P|p} (e_P - 1)`. -/
def totalRamificationAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

end RamificationDivisor
end
