/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Kaehler.Basic

noncomputable section

open Ideal

section SheafIsomorphism

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra k S]
variable [Algebra R S] [IsScalarTower k R S] [NoZeroSMulDivisors R S]
variable [Module.Finite R S]

/-- For a finite morphism of smooth curves over `k`, the induced extension
of function fields is separable. -/
end SheafIsomorphism

section DegreeFormula

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
variable {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
variable [Algebra R S] [NoZeroSMulDivisors R S]

/-- Local degree contribution to the ramification divisor at `p`:
`∑_{P|p} (e_P - 1)`. -/
def localRamificationAt
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) (S : Type*) [CommRing S]
    [IsDomain S] [IsDedekindDomain S] [Algebra R S] : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

set_option linter.unusedSectionVars false in
