/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Algebraic.Integral
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
public import Instance.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz

@[expose] public section

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
