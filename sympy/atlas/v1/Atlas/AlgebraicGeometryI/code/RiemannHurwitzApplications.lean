/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NormalExtension
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NormalExtension
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Height

noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

namespace RiemannHurwitzApplications

section GenusBounds

/-- Prop 39 (Lec, normal domain criterion): the data needed to express
integrality of a fraction in terms of local conditions at height-one primes. -/
structure NormalDomainLocalizationData (R : Type*) [CommRing R] [IsDomain R] where
  isIntegrallyClosed : IsIntegrallyClosed R
  intersection_property :
    ∀ (a b : R), b ≠ 0 →
    (∀ (p : Ideal R), p.IsPrime → p ≠ ⊥ → p.height ≤ (1 : ℕ∞) →
      ∃ (r s : R), s ∉ p ∧ a * s = b * r) →
    ∃ (q : R), a = b * q

/-- Dedekind domains canonically satisfy the normal-domain localization
property: an algebraic Hartogs-type construction recovers the global element
from compatible local fractions. -/
def NormalDomainLocalizationData.ofDedekind
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    NormalDomainLocalizationData R where
  isIntegrallyClosed := inferInstance
  intersection_property := by
    intro a b hb h_local
    have hinj := IsFractionRing.injective R K
    have hb' : algebraMap R K b ≠ 0 := by rwa [Ne, map_eq_zero_iff _ hinj]
    set x := algebraMap R K a * (algebraMap R K b)⁻¹ with hx_def

    have hx_mem : x ∈ Set.range (algebraMap R K) := by
      apply AlgebraicHartogs.algebraicHartogs_dedekind x
      intro v
      obtain ⟨r, s, hs_notin, hrs⟩ := h_local v.asIdeal v.isPrime v.ne_bot
        (by rw [AlgebraicHartogs.height_eq_one_of_prime_ne_bot v.asIdeal v.ne_bot])

      show ∃ (a' s' : R) (_ : s' ∈ v.asIdeal.primeCompl),
        x = algebraMap R K a' * (algebraMap R K s')⁻¹
      refine ⟨r, s, hs_notin, ?_⟩
      have hs' : algebraMap R K s ≠ 0 := by
        intro h0; exact hs_notin (by rw [(map_eq_zero_iff _ hinj).mp h0]; exact v.asIdeal.zero_mem)
      have hmul : algebraMap R K a * algebraMap R K s =
          algebraMap R K b * algebraMap R K r := by rw [← map_mul, ← map_mul, hrs]
      rw [hx_def]
      suffices algebraMap R K a = algebraMap R K r * (algebraMap R K s)⁻¹ * algebraMap R K b by
        rw [this, mul_assoc, mul_inv_cancel₀ hb', mul_one]
      calc algebraMap R K a
          = algebraMap R K a * algebraMap R K s * (algebraMap R K s)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hs', mul_one]
        _ = algebraMap R K b * algebraMap R K r * (algebraMap R K s)⁻¹ := by rw [hmul]
        _ = algebraMap R K r * (algebraMap R K s)⁻¹ * algebraMap R K b := by ring

    obtain ⟨q, hq⟩ := hx_mem
    use q
    apply hinj
    rw [map_mul, hq, hx_def, mul_comm, mul_assoc, inv_mul_cancel₀ hb', mul_one]

example : (2 : ℤ) * 4 - 2 = 3 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 0 - 2 = 2 * (2 * 0 - 2) + 2 := by norm_num

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 1 - 2) + 0 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 11 - 2 = 5 * (2 * 3 - 2) + 0 := by norm_num

example : (mkCurve 0).degK = -2 := by norm_num [mkCurve]

example : (2 : ℤ) * 0 - 2 = 1 * (2 * 0 - 2) + 0 := by norm_num

end Examples

end RiemannHurwitzApplications

end
