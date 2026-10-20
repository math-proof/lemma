/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FiniteApproximation.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Finite approximation at finitely many height-one primes

ATLAS NumberTheoryI item N50, Stages A-B (full finite approximation,
Corollary 3.17, `targets.yaml` lines 317-323). Exact source at the repository pin used here:
[`v1/Atlas/NumberTheoryI/code/Chapter3/FiniteApproximation.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter3/FiniteApproximation.lean#L20-L87),
ATLAS commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

## Source-to-API map

* `FractionalIdeal.exists_elem_eq_valuation_at_primes` covers ATLAS NumberTheoryI:50 /
  Corollary 3.17, `targets.yaml` lines 317-323, and
  `Chapter3/FiniteApproximation.lean` lines 20-87 at commit
  `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`; it is the exact Corollary 3.17 endpoint.
* `Ideal.exists_elem_eq_valuation_at_primes` covers the integral-ideal core
  (source lines 20-87) and serves as the helper for the fractional endpoint.

Scope: this stage proves the integral-ideal helper (source lines 20-87) and the
fractional-ideal Corollary 3.17 endpoint built on it.
-/

open UniqueFactorizationMonoid IsDedekindDomain Ideal Finset

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

theorem Ideal.exists_elem_eq_valuation_at_primes
    {ι : Type*} (s : Finset ι) (ps : ι → HeightOneSpectrum A)
    (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ (0 : A) ∧
      ∀ i ∈ s,
        let e := Multiset.count (normalize (ps i).asIdeal) (normalizedFactors I)
        x ∈ (ps i).asIdeal ^ e ∧ x ∉ (ps i).asIdeal ^ (e + 1) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · obtain ⟨x, hx, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx, hx_ne, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have hle : I * ∏ i ∈ s, (ps i).asIdeal ≤ I := by
    calc I * ∏ i ∈ s, (ps i).asIdeal ≤ I * ⊤ := by gcongr; exact le_top
      _ = I := mul_top I
  have hne : I * ∏ i ∈ s, (ps i).asIdeal ≠ ⊥ :=
    mul_ne_zero hI (Finset.prod_ne_zero_iff.mpr (fun i _ => (ps i).ne_bot))
  obtain ⟨a, ha_sup⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have hmem : a ∈ I :=
    (Ideal.span_le.trans Set.singleton_subset_iff).mp (ha_sup ▸ le_sup_right)
  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha_sup
    obtain ⟨j, hj⟩ := hs
    have heq : I * ∏ i ∈ s, (ps i).asIdeal = I * ⊤ := by rw [ha_sup, mul_top]
    have htop : ∏ i ∈ s, (ps i).asIdeal = ⊤ := mul_left_cancel₀ hI heq
    have hle' : ∏ i ∈ s, (ps i).asIdeal ≤ (ps j).asIdeal := by
      rw [← Finset.mul_prod_erase s _ hj]
      exact Ideal.mul_le_left
    exact (ps j).isPrime.ne_top (le_antisymm le_top (htop ▸ hle'))
  refine ⟨a, hmem, ha_ne, fun i hi => ?_⟩
  have hirr : Irreducible (ps i).asIdeal :=
    (Ideal.prime_of_isPrime (ps i).ne_bot (ps i).isPrime).irreducible
  set e := Multiset.count (normalize (ps i).asIdeal) (normalizedFactors I)
  have hI_le : I ≤ (ps i).asIdeal ^ e := by
    rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
        emultiplicity_eq_count_normalizedFactors hirr hI]
  have hI_not_le : ¬(I ≤ (ps i).asIdeal ^ (e + 1)) := by
    rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
        emultiplicity_eq_count_normalizedFactors hirr hI, not_le]
    exact_mod_cast Nat.lt_succ_iff.mpr le_rfl
  exact ⟨hI_le hmem, fun ha_in =>
    hI_not_le (ha_sup ▸ sup_le
      (show I * ∏ j ∈ s, (ps j).asIdeal ≤ (ps i).asIdeal ^ (e + 1) by
        rw [pow_succ]; gcongr
        rw [← Finset.mul_prod_erase s _ hi]
        exact Ideal.mul_le_left)
      ((Ideal.span_le.trans Set.singleton_subset_iff).mpr ha_in))⟩

theorem FractionalIdeal.exists_elem_eq_valuation_at_primes
    {A K : Type*} [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {ι : Type*} (s : Finset ι) (ps : ι → HeightOneSpectrum A)
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃ x ∈ I, x ≠ (0 : K) ∧
      ∀ i ∈ s,
        FractionalIdeal.count K (ps i) (FractionalIdeal.spanSingleton A⁰ x) =
          FractionalIdeal.count K (ps i) I := by
  obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := FractionalIdeal.ideal_factor_ne_zero hI haJ
  obtain ⟨y, hy, hy0, hval⟩ := Ideal.exists_elem_eq_valuation_at_primes s ps J hJ
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := by
    intro h
    apply ha
    exact hinj (by simpa using h)
  have hyK : algebraMap A K y ≠ 0 := by
    intro h
    apply hy0
    exact hinj (by simpa using h)
  have hx_ne : (algebraMap A K a)⁻¹ * algebraMap A K y ≠ 0 :=
    mul_ne_zero (inv_ne_zero haK) hyK
  refine ⟨(algebraMap A K a)⁻¹ * algebraMap A K y, ?_, hx_ne, ?_⟩
  · rw [haJ]
    exact FractionalIdeal.mem_singleton_mul.mpr
      ⟨algebraMap A K y, FractionalIdeal.mem_coeIdeal_of_mem A⁰ hy, rfl⟩
  · intro i hi
    simp only [normalize_eq] at hval
    obtain ⟨hmem, hnot⟩ := hval i hi
    have hspan_le : Ideal.span {y} ≤ (ps i).asIdeal ^
        Multiset.count (ps i).asIdeal (normalizedFactors J) :=
      (Ideal.span_le.trans Set.singleton_subset_iff).mpr hmem
    have hspan_not : ¬ Ideal.span {y} ≤ (ps i).asIdeal ^
        (Multiset.count (ps i).asIdeal (normalizedFactors J) + 1) :=
      fun hcon => hnot (hcon (Ideal.subset_span rfl))
    have := (ps i).isPrime
    have hcount_span : Multiset.count (ps i).asIdeal
        (normalizedFactors (Ideal.span {y})) =
        Multiset.count (ps i).asIdeal (normalizedFactors J) :=
      Ideal.count_normalizedFactors_eq hspan_le hspan_not
    have hspan_ne : Ideal.span {y} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hy0
    have hassoc : (Associates.mk (ps i).asIdeal).count
        (Associates.mk (Ideal.span {y})).factors =
        (Associates.mk (ps i).asIdeal).count (Associates.mk J).factors := by
      rw [Ideal.count_associates_factors_eq hspan_ne (ps i).isPrime (ps i).ne_bot,
        Ideal.count_associates_factors_eq hJ (ps i).isPrime (ps i).ne_bot,
        hcount_span]
    have hprin : FractionalIdeal.spanSingleton A⁰
          ((algebraMap A K a)⁻¹ * algebraMap A K y) =
        FractionalIdeal.spanSingleton A⁰ (algebraMap A K a)⁻¹ *
          FractionalIdeal.spanSingleton A⁰ (algebraMap A K y) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    have hcoe : FractionalIdeal.spanSingleton A⁰ (algebraMap A K y) =
        (Ideal.span {y} : FractionalIdeal A⁰ K) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    have hPrincipalRepresentation :
        FractionalIdeal.spanSingleton A⁰
          ((algebraMap A K a)⁻¹ * algebraMap A K y) =
        FractionalIdeal.spanSingleton A⁰ (algebraMap A K a)⁻¹ *
          (Ideal.span {y} : FractionalIdeal A⁰ K) := by
      rw [hprin, hcoe]
    have hPrincipal :
        FractionalIdeal.spanSingleton A⁰
          ((algebraMap A K a)⁻¹ * algebraMap A K y) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx_ne
    have hcount_prin :=
      FractionalIdeal.count_well_defined K (ps i) hPrincipal hPrincipalRepresentation
    have hcount_I := FractionalIdeal.count_well_defined K (ps i) hI haJ
    rw [hcount_prin, hcount_I, hassoc]
