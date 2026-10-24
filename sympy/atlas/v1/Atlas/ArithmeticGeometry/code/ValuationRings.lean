/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option maxHeartbeats 800000

open Ideal Submodule

section ValuationRingDef

theorem isValuationSubring_iff_forall_units {K : Type*} [Field K] (R : Subring K) :
    (∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) ↔ (∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) := by
  constructor
  · intro h x _
    exact h x
  · intro h x
    by_cases hx : x = 0
    · left; subst hx; exact R.zero_mem
    · exact h x hx


def ValuationSubring.ofSubring_units {K : Type*} [Field K]
    (R : Subring K) (hR : ∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) :
    ValuationSubring K :=
  ValuationSubring.ofSubring R ((isValuationSubring_iff_forall_units R).mpr hR)

end ValuationRingDef

section Theorem1618

noncomputable example (R : Type*) [CommRing R] [IsLocalRing R] :
    Field (IsLocalRing.ResidueField R) :=
  IsLocalRing.ResidueField.field R


end LocalRing

section RegularLocalDVR

open IsLocalRing Module

def localizationAtPrime (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :=
  Localization.AtPrime 𝔭

instance localizationAtPrime.isLocalRing (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    IsLocalRing (Localization.AtPrime 𝔭) :=
  inferInstance

example (R : Type*) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] :
    R →+* Localization.AtPrime 𝔭 :=
  algebraMap R (Localization.AtPrime 𝔭)

end LocalizationAtPrime

section Definition1620

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable example : LinearOrderedCommGroupWithZero (ValuationRing.ValueGroup R K) :=
  inferInstance

noncomputable def valuationOfValuationRing :
    Valuation K (ValuationRing.ValueGroup R K) :=
  ValuationRing.valuation R K


noncomputable def valuationRingEquivInteger :
    R ≃+* (ValuationRing.valuation R K).integer :=
  ValuationRing.equivInteger R K

end Definition1620

section Definition1627

variable {R : Type*} [CommRing R] {k : Type*} [Field k]

def maximalIdealAtPoint (φ : R →+* k) : Ideal R := RingHom.ker φ


abbrev localRingAtPoint (φ : R →+* k) [(maximalIdealAtPoint φ).IsPrime] :=
  Localization.AtPrime (maximalIdealAtPoint φ)

instance localRingAtPoint_isLocalRing (φ : R →+* k)
    [(maximalIdealAtPoint φ).IsPrime] :
    IsLocalRing (localRingAtPoint φ) :=
  inferInstance


noncomputable def quotient_maximalIdealAtPoint_ringEquiv
    (φ : R →+* k) (hφ : Function.Surjective φ) :
    R ⧸ maximalIdealAtPoint φ ≃+* k :=
  RingHom.quotientKerEquivOfSurjective hφ

def localRingAtPoint_algebraMap (φ : R →+* k)
    [(maximalIdealAtPoint φ).IsPrime] :
    R →+* localRingAtPoint φ :=
  algebraMap R (localRingAtPoint φ)


end Definition1627
