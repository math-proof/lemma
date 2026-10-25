/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiberDegreeBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Data.Set.Card


noncomputable section

open Module Ideal

namespace FiberDegreeBound

section Degree

variable (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The degree of a finite morphism of integral domains, defined as the rank of
fraction fields `[K(A) : K(B)]`. -/
def degree : ℕ := finrank (FractionRing B) (FractionRing A)

/-- `Spec A → Spec B` is unramified over `𝔭` when the fiber attains the degree
upper bound (i.e. the fiber bound of Lem 13 is an equality). -/
def FdbIsUnramifiedOver (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [NoZeroSMulDivisors B A]
    (𝔭 : Ideal B) : Prop :=
  Nat.card {q : Ideal A | q.IsPrime ∧ q.comap (algebraMap B A) = 𝔭} =
    Module.finrank (FractionRing B) (FractionRing A)

/-- `Spec A → Spec B` is ramified over `𝔭` when the fiber bound is a strict
inequality. -/
def FdbIsRamifiedOver (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra B A] [NoZeroSMulDivisors B A]
    (𝔭 : Ideal B) : Prop :=
  ¬ FdbIsUnramifiedOver B A 𝔭

end UnramifiedGeneral

section UnramifiedRamified

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

variable [Algebra R S] [NoZeroSMulDivisors R S]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

variable (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]

variable [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]

variable [Module.Finite R S]

/-- Dedekind-domain version of unramifiedness: the number of primes over `p`
equals `[L : K]`. -/
def FdbIsUnramifiedAt (p : Ideal R) [p.IsMaximal] : Prop :=
  (primesOverFinset p S).card = finrank K L

/-- The Dedekind-domain ramified condition: the fiber bound at `p` is strict. -/
def FdbIsRamifiedAt (p : Ideal R) [p.IsMaximal] : Prop :=
  ¬FdbIsUnramifiedAt (S := S) K L p

end UnramifiedRamified
end FiberDegreeBound
end
