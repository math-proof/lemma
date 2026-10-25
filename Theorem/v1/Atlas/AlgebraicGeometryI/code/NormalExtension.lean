/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Structure.v1.Atlas.AlgebraicGeometryI.code.NormalExtension


namespace AlgebraicHartogs

attribute [instance] HeightOnePrime.isPrime

variable {A : Type*} [CommRing A] [IsDomain A]

/-- In a Dedekind domain, every nonzero prime ideal has height exactly one. -/
theorem height_eq_one_of_prime_ne_bot (p : Ideal A) [hp : p.IsPrime] (hne : p ≠ ⊥) :
    p.height = 1 := by
  apply le_antisymm
  · obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨q, hq_min, hq_le⟩ := Ideal.exists_minimalPrimes_le (J := p)
      ((Ideal.span_le).mpr (Set.singleton_subset_iff.mpr ha_mem))
    have hq_ne : q ≠ ⊥ := by
      intro h; rw [h] at hq_min
      exact ha_ne (Ideal.mem_bot.mp (hq_min.1.2 (Ideal.mem_span_singleton_self a)))
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq_min
    have : q = p := (inferInstance : q.IsPrime).isMaximal hq_ne |>.eq_of_le hp.ne_top hq_le
    rw [← this]
    have : Submodule.IsPrincipal (Ideal.span ({a} : Set A)) := ⟨⟨a, by simp⟩⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq_min
  · rw [ENat.one_le_iff_ne_zero, Ideal.height_eq_primeHeight]
    intro h0
    rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot] at h0
    exact hne (Set.mem_singleton_iff.mp h0)

/-- Algebraic Hartogs theorem for Dedekind domains: a fraction-field element regular at
every height-one prime is globally regular. -/
theorem algebraicHartogs_dedekind (x : K)
    (hx : ∀ v : IsDedekindDomain.HeightOneSpectrum A, x ∈ Localization.subalgebra.ofField K
      v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) :=
  Algebra.mem_bot.mp ((IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot A K) ▸
    (Algebra.mem_iInf.mpr hx))

end AlgebraicHartogs
