import Mathlib
import sympy.Basic
import Instance.v1.Atlas.NumberTheoryI.code.LocalizationDedekind


/--
[submodule_eq_iInf_localizedInField_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma submodule_eq_iInf_localizedInField_maximal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {M : Submodule A K} :
-- imply
  (⨅ (v : MaximalSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M := by
-- proof
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  ·
    intro hx
    let 𝔞 : Ideal A := M.comap (LinearMap.toSpanSingleton A K x)
    by_contra hxM
    have h1 : (1 : A) ∉ 𝔞 := by
      simp only [𝔞, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul]
      exact hxM
    obtain ⟨𝔪, h𝔪max, h𝔞𝔪⟩ := 𝔞.exists_le_maximal (𝔞.ne_top_iff_one.mpr h1)
    obtain ⟨m, hm, s, hs, hsx⟩ := hx ⟨𝔪, h𝔪max⟩
    have hs𝔞 : s ∈ 𝔞 := by
      simp only [𝔞, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      exact hsx ▸ hm
    exact hs (h𝔞𝔪 hs𝔞)
  ·
    intro hx v
    exact ⟨x, hx, 1, v.asIdeal.primeCompl.one_mem', one_smul _ _⟩

/--
[submodule_eq_iInf_localizedInField_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma submodule_eq_iInf_localizedInField_prime
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {M : Submodule A K} :
-- imply
  (⨅ (v : PrimeSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M := by
-- proof
  ext x
  simp only [Submodule.mem_iInf]
  constructor
  ·
    intro hx
    rw [← submodule_eq_iInf_localizedInField_maximal A K M, Submodule.mem_iInf]
    exact fun v => hx ⟨v.asIdeal, v.isMaximal.isPrime⟩
  · intro hx v
    exact ⟨x, hx, 1, v.asIdeal.primeCompl.one_mem', one_smul _ _⟩

/--
[submodule_eq_iInf_localizedInField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma submodule_eq_iInf_localizedInField
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {M : Submodule A K} :
-- imply
  (⨅ (v : MaximalSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M ∧ (⨅ (v : PrimeSpectrum A), M.localizedInField v.asIdeal.primeCompl) = M :=
-- proof
  ⟨submodule_eq_iInf_localizedInField_maximal A K M, submodule_eq_iInf_localizedInField_prime A K M⟩

/--
[subalgebra_iInf_localization_maximal_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma subalgebra_iInf_localization_maximal_eq_bot
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  (⨅ v : MaximalSpectrum A, Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
-- proof
  ext x
  rw [Algebra.mem_bot, Algebra.mem_iInf]
  constructor
  ·
    contrapose
    intro hrange hlocal
    let 𝔞 : Ideal A := (1 : Submodule A K).comap (LinearMap.toSpanSingleton A K x)
    have h1 : (1 : A) ∉ 𝔞 := by simpa [𝔞] using hrange
    obtain ⟨𝔪, h𝔪, h𝔞𝔪⟩ := 𝔞.exists_le_maximal (𝔞.ne_top_iff_one.mpr h1)
    obtain ⟨n, d, hd, rfl⟩ := hlocal ⟨𝔪, h𝔪⟩
    exact hd (h𝔞𝔪 ⟨n, by simp [Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ <|
      (map_ne_zero_iff _ <| IsFractionRing.injective A K).mpr
        fun h ↦ hd (h ▸ 𝔪.zero_mem :)]⟩)
  ·
    rintro ⟨y, rfl⟩ ⟨v, hv⟩
    exact ⟨y, 1, v.ne_top_iff_one.mp hv.ne_top, by rw [map_one, inv_one, mul_one]⟩
set_option linter.unusedSectionVars false in

/--
[ideal_eq_iInf_comap_map_localization_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma ideal_eq_iInf_comap_map_localization_maximal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {I : Ideal A} :
-- imply
  (⨅ 𝔪 : MaximalSpectrum A, (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = I := by
-- proof
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  ·
    intro hx
    by_contra hxI
    have hJ_ne_top : I.colon (Ideal.span {x}) ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one, Ideal.mem_colon_span_singleton]
      simpa using hxI
    obtain ⟨𝔪, h𝔪max, hJ𝔪⟩ := (I.colon (Ideal.span {x})).exists_le_maximal hJ_ne_top
    specialize hx ⟨𝔪, h𝔪max⟩
    rw [Ideal.mem_comap,
      IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    exact hs (hJ𝔪 (Ideal.mem_colon_span_singleton.mpr hsx))
  ·
    intro hxI 𝔪
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI
set_option linter.unusedSectionVars false in

/--
[ideal_eq_iInf_comap_map_localization_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma ideal_eq_iInf_comap_map_localization_prime
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {I : Ideal A} :
-- imply
  (⨅ 𝔭 : PrimeSpectrum A, (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) = I := by
-- proof
  ext x
  simp only [Ideal.mem_iInf]
  constructor
  ·
    intro hx
    rw [← ideal_eq_iInf_comap_map_localization_maximal A I]
    simp only [Ideal.mem_iInf]
    exact fun 𝔪 => hx ⟨𝔪.asIdeal, 𝔪.isMaximal.isPrime⟩
  · intro hxI 𝔭
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hxI
set_option linter.unusedSectionVars false in

/--
[ideal_eq_iInf_comap_map_localization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma ideal_eq_iInf_comap_map_localization
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {I : Ideal A} :
-- imply
  (⨅ 𝔪 : MaximalSpectrum A, (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = (⨅ 𝔭 : PrimeSpectrum A, (I.map (algebraMap A (Localization 𝔭.asIdeal.primeCompl))).comap (algebraMap A (Localization 𝔭.asIdeal.primeCompl))) ∧ (⨅ 𝔪 : MaximalSpectrum A, (I.map (algebraMap A (Localization 𝔪.asIdeal.primeCompl))).comap (algebraMap A (Localization 𝔪.asIdeal.primeCompl))) = I :=
-- proof
  ⟨by rw [ideal_eq_iInf_comap_map_localization_maximal, ideal_eq_iInf_comap_map_localization_prime], ideal_eq_iInf_comap_map_localization_maximal A I⟩
section DedekindDomainCharacterization
variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]

/--
[isDVR_localization_iff_integrallyClosed_dimensionLEOne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma isDVR_localization_iff_integrallyClosed_dimensionLEOne
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A] :
-- imply
  (∀ (P : Ideal A), P ≠ ⊥ → ∀ (_ : P.IsPrime), IsDiscreteValuationRing (Localization.AtPrime P)) ↔ (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) := by
-- proof
  constructor
  ·
    intro h
    have : IsDedekindDomainDvr A := { is_dvr_at_nonzero_prime := h }
    exact ⟨inferInstance, inferInstance⟩
  ·
    intro ⟨hic, hdim⟩
    have : IsDedekindDomain A := { }
    intro P hP hPprime
    exact (IsDedekindDomain.isDedekindDomainDvr A).is_dvr_at_nonzero_prime P hP hPprime
end DedekindDomainCharacterization
section DedekindDomain
variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]

/--
[integrallyClosed_dimensionLEOne_iff_isDedekindDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma integrallyClosed_dimensionLEOne_iff_isDedekindDomain
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A] :
-- imply
  (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) ↔ IsDedekindDomain A := by
-- proof
  constructor
  · rintro ⟨hic, hdim⟩
    exact { }
  · intro h
    exact ⟨inferInstance, inferInstance⟩
end DedekindDomain
section PrincipalIdealDedekind

/--
[pid_isDedekindDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean)
-/
@[path]
lemma pid_isDedekindDomain
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R] :
-- imply
  IsDedekindDomain R :=
-- proof
  inferInstance


-- created on 2026-10-23
