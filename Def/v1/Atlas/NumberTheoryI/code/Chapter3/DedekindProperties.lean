/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/DedekindProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
open Ideal


namespace DedekindDomainEquiv

variable (A : Type*) [CommRing A] [IsDomain A]

def CondIntegrallyClosed : Prop := IsDedekindDomain A

def CondDvrLocalizations : Prop := IsDedekindDomainDvr A

def CondInvertibleIdeals : Prop := IsDedekindDomainInv A

def CondPrimeFactorization : Prop :=
  ∀ (I : Ideal A), I ≠ ⊥ → ∃ (s : Multiset (Ideal A)), (∀ p ∈ s, Prime p) ∧ s.prod = I

def CondContainIsDivide : Prop :=
  IsNoetherianRing A ∧ ∀ (I J : Ideal A), I ∣ J ↔ J ≤ I

def CondPrincipalProduct : Prop :=
  ∀ (I : Ideal A), I ≠ ⊥ → ∃ (J : Ideal A), (I * J).IsPrincipal ∧ I * J ≠ ⊥

def CondQuotientPIR : Prop :=
  ∀ (I : Ideal A), I ≠ ⊥ → IsPrincipalIdealRing (A ⧸ I)

def CondTwoGenerator : Prop :=
  ∀ (I : Ideal A) (a : A), I ≠ ⊥ → a ≠ 0 → a ∈ I → ∃ b : A, I = Ideal.span {a, b}

def localizationRingEquiv (h : K ≃ₐ[A] K') :
    FractionalIdeal A⁰ K ≃+* FractionalIdeal A⁰ K' :=
  FractionalIdeal.mapEquiv h

noncomputable def fractionFieldEquiv : K ≃ₐ[A] K' :=
  IsLocalization.algEquiv A⁰ K K'

end DedekindDomainEquiv
