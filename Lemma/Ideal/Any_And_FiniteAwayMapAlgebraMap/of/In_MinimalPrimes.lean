import Mathlib
import sympy.Basic
open Polynomial
open IsLocalRing
open scoped TensorProduct


private lemma isIntegral_of_isLocalRing_of_forall_isNilpotent
  [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Algebra.QuasiFinite R S]
-- given
  (h : ∀ x ∈ maximalIdeal R, IsNilpotent x) :
-- imply
  Algebra.IsIntegral R S := by
-- proof
  classical
  set I : Ideal S := (maximalIdeal R).map (algebraMap R S)
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)
  let _ : Module.Finite R (S ⧸ I) :=
    have _ : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  have hInil : I ≤ nilradical S := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    apply mem_nilradical.mpr ((h x hx).map (algebraMap R S))
  refine ⟨fun x => ?_⟩
  obtain ⟨F, hFm, hF⟩ : IsIntegral R (Ideal.Quotient.mkₐ R I x) := Algebra.IsIntegral.isIntegral _
  have hx : aeval x F ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
      aeval_def]
    apply hF
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hInil hx)
  refine ⟨F ^ n, hFm.pow n, ?_⟩
  rw [← aeval_def, map_pow, hn]

private lemma exists_not_mem_isIntegral_smul
  [CommRing R] [CommRing A] [Algebra R A] [Algebra.QuasiFinite R A]
  {p : Ideal R}
  {a : A}
-- given
  (hp : p ∈ minimalPrimes R) :
-- imply
  ∃ t : R, t ∉ p ∧ IsIntegral R (t • a) := by
-- proof
  classical
  let _ : p.IsPrime := hp.1.1
  let Rp := Localization.AtPrime p
  let S := Rp ⊗[R] A
  have hnil : ∀ x ∈ maximalIdeal Rp, IsNilpotent x := by
    intro x hx
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Rp) p ⊥ hp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, ← hrad, Ideal.map_bot,
      Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    simpa using hn
  let _ : Algebra.IsIntegral Rp S := isIntegral_of_isLocalRing_of_forall_isNilpotent hnil
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl
    (Rₘ := Rp) ((1 : Rp) ⊗ₜ[R] a : S) (Algebra.IsIntegral.isIntegral _)
  obtain ⟨G, hGm, hG⟩ := hm
  have h1 : (m • ((1 : Rp) ⊗ₜ[R] a) : S) = Algebra.TensorProduct.includeRight ((m : R) • a) := by
    rw [Algebra.TensorProduct.includeRight_apply, Submonoid.smul_def, TensorProduct.tmul_smul]
  have h2 : (TensorProduct.mk R Rp A 1) (aeval ((m : R) • a) G) = 0 := by
    rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply,
      ← h1, aeval_def]
    apply hG
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (TensorProduct.mk R Rp A 1)).mp h2
  refine ⟨s * m, fun h => (hp.1.1.mem_or_mem h).elim s.2 m.2, ?_⟩
  have h3 : aeval ((m : R) • a) (C (s : R) * G) = 0 := by
    rw [map_mul, aeval_C, ← Algebra.smul_def, ← Submonoid.smul_def]
    apply hs
  have := isIntegral_leadingCoeff_smul (C (s : R) * G) ((m : R) • a) h3
  rwa [leadingCoeff_mul_monic hGm, leadingCoeff_C, smul_smul] at this

private lemma finite_awayMap_of_forall_isIntegral_smul
  {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {gens : Finset A}
  {t : A → R}
-- given
  (hgens : Algebra.adjoin R (gens : Set A) = ⊤)
  (ht : ∀ a ∈ gens, IsIntegral R (t a • a)) :
-- imply
  (Localization.awayMap (algebraMap R A) (∏ a ∈ gens, t a)).Finite := by
-- proof
  classical
  set r : R := ∏ a ∈ gens, t a with hr
  let Rr := Localization.Away r
  let Ar := Localization.Away (algebraMap R A r)
  let φ : Rr →+* Ar := Localization.awayMap (algebraMap R A) r
  let _ : Algebra Rr Ar := φ.toAlgebra
  let _ : IsScalarTower R Rr Ar := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R A Ar]
    apply (IsLocalization.map_eq _ x).symm
  let _ : Algebra.FiniteType R A := ⟨⟨gens, hgens⟩⟩
  have hft : φ.FiniteType :=
    RingHom.localization_away_map_finiteType R A Rr Ar (algebraMap R A) r
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let ψ : A →ₐ[R] Ar := IsScalarTower.toAlgHom R A Ar
  have hr_unit : IsUnit (algebraMap R Rr r) := IsLocalization.Away.algebraMap_isUnit r
  have hgen : ∀ a ∈ gens, IsIntegral Rr (ψ a) := by
    intro a ha
    have hu : IsUnit (algebraMap R Rr (t a)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem t ha)) hr_unit
    obtain ⟨u, hu'⟩ := hu
    have h1 : IsIntegral Rr (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      have := (ht a ha).map ψ
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R Rr Ar] at this
      apply this.tower_top
    have h2 : ψ a = algebraMap Rr Ar ↑u⁻¹ * (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      rw [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul]
    rw [h2]
    apply isIntegral_algebraMap.mul h1
  have hA : ∀ a : A, IsIntegral Rr (ψ a) := by
    have hle : Algebra.adjoin R (ψ '' (gens : Set A)) ≤
        (integralClosure Rr Ar).restrictScalars R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨a, ha, rfl⟩
      apply (Subalgebra.mem_restrictScalars R).mpr (hgen a ha)
    intro a
    apply (Subalgebra.mem_restrictScalars R).mp
      (hle (by rw [← AlgHom.map_adjoin, hgens]; apply Subalgebra.mem_map.mpr ⟨a, Algebra.mem_top, rfl⟩))
  apply RingHom.IsIntegral.to_finite _ hft
  intro x
  change IsIntegral Rr x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap R A r)) x
  change _root_.IsIntegral Rr (IsLocalization.mk' Ar a s)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hu : IsUnit (algebraMap R Rr (r ^ n)) := by
    rw [map_pow]
    apply hr_unit.pow n
  obtain ⟨u, hu'⟩ := hu
  have hx : IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u = ψ a := by
    rw [hu', ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A Ar, map_pow, hn]
    apply IsLocalization.mk'_spec Ar a s
  have key : IsIntegral Rr (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
    rw [hx]
    apply hA a
  have : IsLocalization.mk' Ar a s =
      algebraMap Rr Ar ↑u⁻¹ * (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
    rw [mul_comm (IsLocalization.mk' Ar a s), ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
      one_mul]
  rw [this]
  apply isIntegral_algebraMap.mul key


/--
[Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.lean)
-/
@[path]
private lemma main
  {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [Algebra.QuasiFinite R A]
  {p : Ideal R}
-- given
  (hp : p ∈ minimalPrimes R) :
-- imply
  ∃ r : R, r ∉ p ∧ (Localization.awayMap (algebraMap R A) r).Finite := by
-- proof
  classical
  let _ : p.IsPrime := hp.1.1
  obtain ⟨gens, hgens⟩ := (inferInstance : Algebra.FiniteType R A).out
  choose t ht hti using fun a : A => exists_not_mem_isIntegral_smul (a := a) hp
  refine ⟨∏ a ∈ gens, t a, ?_, finite_awayMap_of_forall_isIntegral_smul (t := t) hgens (fun a _ => hti a)⟩
  rw [(show p.IsPrime from hp.1.1).prod_mem_iff]
  simpa using fun a (_ : a ∈ gens) => ht a


-- created on 2026-10-13
