import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma factorPow_evalₐ
  [CommRing R]
  {I : Ideal R}
  {m n : ℕ}
  {x : AdicCompletion I R}
  -- given
  (hle : m ≤ n) :
  -- imply
  Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  -- proof
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  apply AdicCompletion.Ideal.mk_eq_mk I hle a

private lemma exists_ringEquiv
  [CommRing R] [CommRing S]
  {I : Ideal R}
  {J : Ideal S}
  {e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n}
  -- given
  (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ I ^ n), e m (Ideal.Quotient.factorPow I hle x) = Ideal.Quotient.factorPow J hle (e n x)) :
  -- imply
  ∃ E : AdicCompletion I R ≃+* AdicCompletion J S, ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x) := by
  -- proof
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : S ⧸ J ^ n), (e m).symm (Ideal.Quotient.factorPow J hle y) = Ideal.Quotient.factorPow I hle ((e n).symm y) := by
    intro m n hle y
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  have hFcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp ((e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) = (e m).toRingHom.comp (AdicCompletion.evalₐ I m).toRingHom := by
    intro m n hle
    ext x
    show Ideal.Quotient.factorPow J hle (e n (AdicCompletion.evalₐ I n x)) = e m (AdicCompletion.evalₐ I m x)
    rw [← he, factorPow_evalₐ]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) hFcomp
  have hGcomp : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp ((e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) = (e m).symm.toRingHom.comp (AdicCompletion.evalₐ J m).toRingHom := by
    intro m n hle
    ext y
    show Ideal.Quotient.factorPow I hle ((e n).symm (AdicCompletion.evalₐ J n y)) = (e m).symm (AdicCompletion.evalₐ J m y)
    rw [← he', factorPow_evalₐ]
  let G : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) hGcomp
  have hF : ∀ n x, AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom J
      (fun k => (e k).toRingHom.comp (AdicCompletion.evalₐ I k).toRingHom) hFcomp n x
  have hG : ∀ n y, AdicCompletion.evalₐ I n (G y) = (e n).symm (AdicCompletion.evalₐ J n y) :=
    fun n y => AdicCompletion.evalₐ_liftRingHom I
      (fun k => (e k).symm.toRingHom.comp (AdicCompletion.evalₐ J k).toRingHom) hGcomp n y
  refine ⟨RingEquiv.ofRingHom F G ?_ ?_, hF⟩
  ·
    apply RingHom.ext
    intro y
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  ·
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

private lemma apply_of_eq_of
  [CommRing R] [CommRing S]
  {I : Ideal R}
  {J : Ideal S}
  {e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n}
  {E : AdicCompletion I R ≃+* AdicCompletion J S}
  {θ : R → S}
  {r : R}
  -- given
  (hE : ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x))
  (hθ : ∀ (n : ℕ) (r : R), e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (θ r)) :
  -- imply
  E (AdicCompletion.of I R r) = AdicCompletion.of J S (θ r) := by
  -- proof
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, AdicCompletion.evalₐ_of, hθ, AdicCompletion.evalₐ_of]

/--
[Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv.lean)
-/
@[path]
private lemma main
  {C : Type u} [CommRing C]
  {𝔪 : Ideal C} [𝔪.IsMaximal] :
  -- imply
  ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) (Localization.AtPrime 𝔪) ≃+* AdicCompletion 𝔪 C, ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _ (algebraMap C (Localization.AtPrime 𝔪) c)) = algebraMap C (AdicCompletion 𝔪 C) c := by
  -- proof
  classical
  have hmap : ∀ n : ℕ, (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪)) = (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n := by
    intro n
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  have hunit : ∀ (n : ℕ) (s : C), s ∉ 𝔪 → IsUnit (Ideal.Quotient.mk (𝔪 ^ n) s) := by
    intro n s hs
    obtain ⟨y, i, hi, hyi⟩ := (‹𝔪.IsMaximal›).exists_inv hs
    apply isUnit_of_mul_isUnit_right
    rw [← map_mul, eq_sub_of_add_eq hyi, map_sub, map_one]
    apply IsNilpotent.isUnit_one_sub
    refine ⟨n, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.pow_mem_pow hi n
  have hU : ∀ n : ℕ, Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl ≤ IsUnit.submonoid (C ⧸ 𝔪 ^ n) := by
    intro n x hx
    rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    apply hunit n s hs
  let d : ∀ n : ℕ, C ⧸ 𝔪 ^ n ≃+* Localization.AtPrime 𝔪 ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n := fun n => (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl) (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).toRingEquiv.trans (Ideal.quotEquivOfEq (hmap n))
  have hd_mk : ∀ (n : ℕ) (c : C), d n (Ideal.Quotient.mk (𝔪 ^ n) c) = Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime 𝔪) c) := by
    intro n c
    have h := (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl) (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).commutes (Ideal.Quotient.mk (𝔪 ^ n) c)
    rw [Algebra.algebraMap_self, RingHom.id_apply, Ideal.Quotient.algebraMap_quotient_map_quotient] at h
    show Ideal.quotEquivOfEq (hmap n) (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl) (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n) (Ideal.Quotient.mk (𝔪 ^ n) c)) = _
    rw [h, Ideal.quotEquivOfEq_mk]
  have hd : ∀ {m n : ℕ} (hle : m ≤ n) (x : C ⧸ 𝔪 ^ n), d m (Ideal.Quotient.factorPow 𝔪 hle x) = Ideal.Quotient.factorPow _ hle (d n x) := by
    intro m n hle x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, hd_mk, hd_mk, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := exists_ringEquiv (I := 𝔪) (J := IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) (e := d) hd
  refine ⟨E.symm, fun c => ?_⟩
  apply E.injective
  rw [RingEquiv.apply_symm_apply, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]
  apply (apply_of_eq_of (e := d) (E := E) (θ := algebraMap C (Localization.AtPrime 𝔪)) (r := c) hE hd_mk).symm


-- created on 2026-10-20
