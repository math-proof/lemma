import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  {M : Type u} [Field M] [Algebra C M]
private lemma coe_mem (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (b : ↥(integralClosure C M)) : (b : M) ∈ V := by
  have hb : IsIntegral C (b : M) := b.2
  set φ : C →+* ↥V := (algebraMap C M).codRestrict V hCV with hφ
  have hcomp : (algebraMap (↥V) M).comp φ = algebraMap C M := RingHom.ext fun _ => rfl
  have hb' : IsIntegral (↥V) (b : M) := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map φ, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := M)).mp hb'
  rw [← hy]
  exact y.2
private noncomputable def psi (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V) :
    ↥(integralClosure C M) →+* ↥V :=
  (algebraMap (↥(integralClosure C M)) M).codRestrict V (coe_mem V hCV)
private noncomputable def PP (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V) :
    Ideal ↥(integralClosure C M) :=
  (IsLocalRing.maximalIdeal ↥V).comap (psi V hCV)
private lemma mem_PP_iff (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (b : ↥(integralClosure C M)) :
    b ∈ PP V hCV ↔ (b : M) ∈ V.nonunits := by
  rw [PP, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl
instance PP_isPrime (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V) :
    (PP V hCV).IsPrime := by
  unfold PP; infer_instance
private lemma under_PP (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (PP V hCV).under C = IsLocalRing.maximalIdeal C := by
  ext c
  rw [Ideal.under_def, Ideal.mem_comap, mem_PP_iff, ← hCVmax]
  rfl
private lemma PP_liesOver (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (PP V hCV).LiesOver (IsLocalRing.maximalIdeal C) :=
  ⟨(under_PP V hCV hCVmax).symm⟩
private lemma coe_ne_zero_of_not_mem (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (s : ↥(integralClosure C M)) (hs : s ∉ PP V hCV) : (s : M) ≠ 0 := by
  intro h0
  apply hs
  have : s = 0 := by exact_mod_cast h0
  rw [this]; exact Ideal.zero_mem _
variable {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
  {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
include K in
private lemma exists_unif (V : ValuationSubring M)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    ∃ ϖ : C, ϖ ≠ 0 ∧ algebraMap C M ϖ ≠ 0 ∧ algebraMap C M ϖ ∈ V.nonunits := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  refine ⟨ϖ, hϖ.ne_zero, ?_, (hCVmax ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)⟩
  rw [IsScalarTower.algebraMap_apply C K M]
  exact (map_ne_zero (algebraMap K M)).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective C K)).mpr hϖ.ne_zero)
include K in
private lemma PP_ne_bot (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    PP V hCV ≠ ⊥ := by
  obtain ⟨ϖ, hϖ0, hϖM, hϖV⟩ := exists_unif K V hCVmax
  intro h
  have hmem : algebraMap C (↥(integralClosure C M)) ϖ ∈ PP V hCV := by
    rw [mem_PP_iff]
    simpa using hϖV
  rw [h, Ideal.mem_bot] at hmem
  apply hϖM
  have := congrArg (fun b : ↥(integralClosure C M) => (b : M)) hmem
  simpa using this
include K in
private lemma V_ne_top (V : ValuationSubring M)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    V ≠ ⊤ := by
  obtain ⟨ϖ, hϖ0, hϖM, hϖV⟩ := exists_unif K V hCVmax
  intro h
  rcases (ValuationSubring.mem_nonunits_iff_or V).mp hϖV with h0 | hinv
  · exact hϖM h0
  · exact hinv (h.symm ▸ ValuationSubring.mem_top _)
variable [FiniteDimensional K M] [Algebra.IsSeparable K M]
include K in
private lemma PP_isMaximal (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (PP V hCV).IsMaximal := by
  let _ : IsDedekindDomain ↥(integralClosure C M) := integralClosure.isDedekindDomain C K M
  exact Ideal.IsPrime.isMaximal inferInstance (PP_ne_bot K V hCV hCVmax)
include K in
private lemma helper_main (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (∀ b : ↥(integralClosure C M), (b : M) ∈ V) ∧
    ∃ P : Ideal ↥(integralClosure C M), P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal C) ∧
      (∀ b : ↥(integralClosure C M), b ∈ P ↔ (b : M) ∈ V.nonunits) ∧
      (∀ y : M, y ∈ V ↔ ∃ b s : ↥(integralClosure C M), s ∉ P ∧ y * (s : M) = (b : M)) := by
  let hDD : IsDedekindDomain ↥(integralClosure C M) := integralClosure.isDedekindDomain C K M
  let hFR : IsFractionRing ↥(integralClosure C M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension C K M ↥(integralClosure C M)
  refine ⟨coe_mem V hCV, PP V hCV, PP_isMaximal K V hCV hCVmax, PP_liesOver V hCV hCVmax,
    mem_PP_iff V hCV, ?_⟩
  let v : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure C M) :=
    ⟨PP V hCV, inferInstance, PP_ne_bot K V hCV hCVmax⟩
  have hle : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    have ha : algebraMap (↥(integralClosure C M)) M a ∈ V := coe_mem V hCV a
    have hsV : algebraMap (↥(integralClosure C M)) M s ∈ V := coe_mem V hCV s
    have hs' : (s : M) ∉ V.nonunits := fun h => hs ((mem_PP_iff V hCV s).mpr h)
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hs'
    exact V.mul_mem _ _ ha hs'.2
  have heq : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hle (V_ne_top K V hCVmax)
  intro y
  have key : y ∈ V ↔ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M v := by
    rw [heq]
  rw [key]
  constructor
  · rintro ⟨b, s, hs, rfl⟩
    refine ⟨b, s, hs, ?_⟩
    rw [← eq_mul_inv_iff_mul_eq₀ (coe_ne_zero_of_not_mem V hCV s hs)]
    rfl
  · rintro ⟨b, s, hs, h⟩
    refine ⟨b, s, hs, ?_⟩
    change y = (b : M) * ((s : M))⁻¹
    rw [eq_mul_inv_iff_mul_eq₀ (coe_ne_zero_of_not_mem V hCV s hs)]
    exact h
/--
[ValuationSubring_integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing.lean)
-/
@[path]
private lemma main
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C) :
    (∀ b : ↥(integralClosure C M), (b : M) ∈ V) ∧
    ∃ P : Ideal ↥(integralClosure C M), P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal C) ∧
      (∀ b : ↥(integralClosure C M), b ∈ P ↔ (b : M) ∈ V.nonunits) ∧
      (∀ y : M, y ∈ V ↔ ∃ b s : ↥(integralClosure C M), s ∉ P ∧ y * (s : M) = (b : M)) := by
  exact helper_main K V hCV hCVmax

-- created on 2026-10-21
