import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma map_maximalIdeal [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) : (maximalIdeal R).map (e : R →+* S) = maximalIdeal S := by
  apply IsLocalRing.eq_maximalIdeal
  apply Ideal.map_isMaximal_of_equiv e

private lemma map_maximalIdeal_pow [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) : maximalIdeal S ^ n = ((maximalIdeal R) ^ n).map (e : R →+* S) := by
  rw [Ideal.map_pow, map_maximalIdeal]

private noncomputable def quotEquiv [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) : R ⧸ maximalIdeal R ^ n ≃+* S ⧸ maximalIdeal S ^ n := Ideal.quotientEquiv (maximalIdeal R ^ n) (maximalIdeal S ^ n) e (map_maximalIdeal_pow e n)

private lemma quotEquiv_mk [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : R) : quotEquiv e n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) := Ideal.quotientEquiv_mk _ _ _ _ x

private lemma factorPow_evalₐ [CommRing R] [IsLocalRing R] (I : Ideal R) {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) : Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨y, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  apply AdicCompletion.Ideal.mk_eq_mk I hle y

private noncomputable def fam [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) : AdicCompletion (maximalIdeal R) R →+* S ⧸ maximalIdeal S ^ n := ((quotEquiv e n).toRingHom).comp (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom

private lemma fam_compat [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow (maximalIdeal S) hle).comp (fam e n) = fam e m := by
  intro m n hle
  simp [fam]
  apply RingHom.ext
  intro x
  simp [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
  rw [← factorPow_evalₐ (maximalIdeal R) hle x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n x)
  rw [← hy]
  simp [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, quotEquiv_mk]

private noncomputable def complMap [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal S) S := AdicCompletion.liftRingHom (maximalIdeal S) (fam e) (fam_compat e)

private lemma evalₐ_complMap [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) : AdicCompletion.evalₐ (maximalIdeal S) n (complMap e x) = quotEquiv e n (AdicCompletion.evalₐ (maximalIdeal R) n x) := by
  show AdicCompletion.evalₐ (maximalIdeal S) n (AdicCompletion.liftRingHom (maximalIdeal S) (fam e) (fam_compat e) x) = _
  rw [AdicCompletion.evalₐ_liftRingHom (maximalIdeal S) (fam e) (fam_compat e) n x]
  rfl

private lemma complMap_symm_complMap [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (x : AdicCompletion (maximalIdeal R) R) : complMap e.symm (complMap e x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, evalₐ_complMap]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n x)
  rw [← hy, quotEquiv_mk, quotEquiv_mk, RingEquiv.symm_apply_apply]

private lemma complMap_of [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (r : R) : complMap e (AdicCompletion.of (maximalIdeal R) R r) = AdicCompletion.of (maximalIdeal S) S (e r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_complMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, quotEquiv_mk]

/--
[IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (e : R ≃+* S) :
  -- imply
  ∃ ê : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S, ∀ r : R, ê (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by
  -- proof
  refine ⟨RingEquiv.ofRingHom (complMap e) (complMap e.symm) ?_ ?_, ?_⟩
  ·
    apply RingHom.ext
    intro x
    have := complMap_symm_complMap e.symm x
    rw [RingEquiv.symm_symm] at this
    apply this
  ·
    apply RingHom.ext
    intro x
    apply complMap_symm_complMap e x
  ·
    intro r
    show complMap e (AdicCompletion.of (IsLocalRing.maximalIdeal R) R r) = AdicCompletion.of (IsLocalRing.maximalIdeal S) S (e r)
    apply complMap_of e r


-- created on 2026-10-20
