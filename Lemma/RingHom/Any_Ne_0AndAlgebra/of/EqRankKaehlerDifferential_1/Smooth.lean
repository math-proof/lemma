import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped TensorProduct nonZeroDivisors


private lemma rankAtStalk_eq_one
  {S : Type} [CommRing S] [IsDomain S]
  {M : Type} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] [Module.Flat S M]
  {p : PrimeSpectrum S}
-- given
  (hrank : Module.rank S M = 1) :
-- imply
  Module.rankAtStalk M p = 1 := by
-- proof
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply hx
    rw [h0]
    apply Submodule.zero_mem
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S))
    (LocalizedModule (⊥ : Ideal S).primeCompl M) = 1 := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal S).primeCompl)
        (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl)
        (f := LocalizedModule.mkLinearMap (⊥ : Ideal S).primeCompl M) (hp := hle), hrank]
  show Module.finrank (Localization.AtPrime (⊥ : Ideal S))
    (LocalizedModule (⊥ : Ideal S).primeCompl M) = 1
  apply Module.finrank_eq_of_rank_eq (by rw [hr, Nat.cast_one])

private lemma mem_smul_top_of_mk_mem
  {S : Type} [CommRing S]
  {M : Type} [AddCommGroup M] [Module S M]
  {𝔪 : Ideal S} [𝔪.IsMaximal]
  {x : M}
-- given
  (h : LocalizedModule.mk x (1 : 𝔪.primeCompl) ∈
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) • (⊤ : Submodule (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl M))) :
-- imply
  x ∈ 𝔪 • (⊤ : Submodule S M) := by
-- proof
  have key : (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) • (⊤ : Submodule (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl M)) = (𝔪 • (⊤ : Submodule S M)).localized'
        (Localization.AtPrime 𝔪) 𝔪.primeCompl (LocalizedModule.mkLinearMap 𝔪.primeCompl M) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [key, Submodule.mem_localized', IsLocalizedModule.mk_eq_mk'] at h
  obtain ⟨m, hm, s, hms⟩ := h
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hms
  obtain ⟨c, hc⟩ := hms
  have hcx : ((c : S) * (s : S)) • x = (c : S) • m := by
    have := hc
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    apply this
  have hnot : (c : S) * (s : S) ∉ 𝔪 := ‹𝔪.IsMaximal›.isPrime.mul_notMem c.2 s.2
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› hnot
  have hx : x = y • (((c : S) * (s : S)) • x) + i • x := by
    rw [smul_smul, ← add_smul, hyi, one_smul]
  rw [hx, hcx]
  apply Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hm))
    (Submodule.smul_mem_smul hi Submodule.mem_top)

private lemma bijective_smul_mk
  {S : Type} [CommRing S]
  {M : Type} [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Flat S M]
  {𝔪 : Ideal S} [𝔪.IsMaximal]
  {x : M}
-- given
  (h0 : Module.rankAtStalk M ⟨𝔪, inferInstance⟩ = 1)
  (hx : x ∉ 𝔪 • (⊤ : Submodule S M)) :
-- imply
  Function.Bijective (fun s : Localization.AtPrime 𝔪 => s • LocalizedModule.mk x (1 : 𝔪.primeCompl)) := by
-- proof
  let _ : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  set ω : LocalizedModule 𝔪.primeCompl M := LocalizedModule.mk x (1 : 𝔪.primeCompl) with hω
  have h1' : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = 1 := h0
  let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) h1'
  set u : Localization.AtPrime 𝔪 := b.repr ω 0 with hu
  have hωu : ω = u • b 0 := by
    have := b.sum_repr ω
    rw [Fin.sum_univ_one] at this
    apply this.symm
  have hunit : IsUnit u := by
    by_contra hnu
    apply hx
    apply mem_smul_top_of_mk_mem (𝔪 := 𝔪) (x := x)
    rw [← hω, hωu]
    apply Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal u).2 (mem_nonunits_iff.2 hnu))
      Submodule.mem_top
  have hrepr : ∀ s : Localization.AtPrime 𝔪, b.repr (s • ω) 0 = s * u := by
    intro s
    rw [hωu, smul_smul, map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_eq_same]
  constructor
  ·
    intro s s' hss'
    have := congrArg (fun z => b.repr z 0) hss'
    simp only [hrepr] at this
    apply hunit.mul_left_injective this
  ·
    intro y
    refine ⟨b.repr y 0 * ↑hunit.unit⁻¹, ?_⟩
    show (b.repr y 0 * ↑hunit.unit⁻¹) • ω = y
    rw [hωu, smul_smul, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have := b.sum_repr y
    rw [Fin.sum_univ_one] at this
    apply this

private lemma exists_eq_tmul_D_X
  {S : Type} [CommRing S] [Algebra ℂ[X] S]
  {z : S ⊗[ℂ[X]] Ω[ℂ[X]⁄ℂ]} :
-- imply
  ∃ a : S, z = a ⊗ₜ[ℂ[X]] KaehlerDifferential.D ℂ ℂ[X] X := by
-- proof
  induction z using TensorProduct.inductionOn with
  | tmul s ω =>
    refine ⟨KaehlerDifferential.polynomialEquiv ℂ ω • s, ?_⟩
    conv_lhs => rw [← (KaehlerDifferential.polynomialEquiv ℂ).symm_apply_apply ω,
      KaehlerDifferential.polynomialEquiv_symm]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨a₁, rfl⟩ := h₁
    obtain ⟨a₂, rfl⟩ := h₂
    refine ⟨a₁ + a₂, ?_⟩
    rw [TensorProduct.add_tmul]

private lemma D_algebraMap_eq_zero
  {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  {r : R} :
-- imply
  KaehlerDifferential.D R A (algebraMap R A r) = 0 := by
-- proof
  rw [Algebra.algebraMap_eq_smul_one, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

private lemma notMem_support_kaehlerDifferential
  {S : Type} [CommRing S] [Algebra ℂ S] [Algebra ℂ[X] S] [IsScalarTower ℂ ℂ[X] S]
  {t : S} {𝔪 : Ideal S} [𝔪.IsMaximal]
-- given
  (hX : algebraMap ℂ[X] S X = t)
  (hψ : Function.Surjective (fun s : Localization.AtPrime 𝔪 =>
    s • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl))) :
-- imply
  (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Ω[S⁄ℂ[X]]) := by
-- proof
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective ℂ ℂ[X] S m
  obtain ⟨sₘ, hsₘ⟩ := hψ (LocalizedModule.mk ω₁ 1)
  obtain ⟨⟨a, c⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl sₘ
  have h2 := congrArg (fun z => algebraMap S (Localization.AtPrime 𝔪) (c : S) • z) hsₘ
  simp only at h2
  rw [smul_smul, IsLocalization.mk'_spec', algebraMap_smul, algebraMap_smul, LocalizedModule.smul'_mk,
    LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h2
  obtain ⟨u, hu⟩ := h2
  have hu' : ((u : S) * (c : S)) • ω₁ = ((u : S) * a) • KaehlerDifferential.D ℂ S t := by
    have := hu
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    apply this.symm
  refine ⟨(u : S) * (c : S), ‹𝔪.IsMaximal›.isPrime.mul_notMem u.2 c.2, ?_⟩
  rw [← LinearMap.map_smul, hu', LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply,
    ← hX, D_algebraMap_eq_zero, smul_zero]

private lemma notMem_support_h1Cotangent
  {S : Type} [CommRing S] [Algebra ℂ S] [Algebra.FormallySmooth ℂ S] [Algebra ℂ[X] S] [IsScalarTower ℂ ℂ[X] S]
  {t : S} {𝔪 : Ideal S} [𝔪.IsMaximal]
-- given
  (hX : algebraMap ℂ[X] S X = t)
  (hψ : Function.Injective (fun s : Localization.AtPrime 𝔪 =>
    s • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl))) :
-- imply
  (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉
    Module.support S (Algebra.H1Cotangent ℂ[X] S) := by
-- proof
  rw [Module.notMem_support_iff']
  intro h
  have hinj : Function.Injective (Algebra.H1Cotangent.δ ℂ ℂ[X] S) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ (R := ℂ) (S := ℂ[X]) (T := S) z).1 hz
    rw [Subsingleton.elim w 0, LinearMap.map_zero]
  have hδ0 : KaehlerDifferential.mapBaseChange ℂ ℂ[X] S (Algebra.H1Cotangent.δ ℂ ℂ[X] S h) = 0 :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := ℂ) (S := ℂ[X]) (T := S) _).2 ⟨h, rfl⟩
  obtain ⟨a, ha⟩ := exists_eq_tmul_D_X (z := Algebra.H1Cotangent.δ ℂ ℂ[X] S h)
  rw [ha, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX] at hδ0
  have h0 : algebraMap S (Localization.AtPrime 𝔪) a = 0 := by
    apply hψ
    show algebraMap S (Localization.AtPrime 𝔪) a •
        LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl) =
      (0 : Localization.AtPrime 𝔪) • LocalizedModule.mk (KaehlerDifferential.D ℂ S t) (1 : 𝔪.primeCompl)
    rw [algebraMap_smul, LocalizedModule.smul'_mk, hδ0, LocalizedModule.zero_mk, zero_smul]
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔪.primeCompl (Localization.AtPrime 𝔪) a).1 h0
  refine ⟨c, c.2, hinj ?_⟩
  rw [LinearMap.map_smul, map_zero, ha, TensorProduct.smul_tmul', smul_eq_mul, hc, TensorProduct.zero_tmul]


/--
[Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
  {σ₀ : S →ₐ[ℂ] ℂ} {t : S}
-- given
  (hsm : Algebra.Smooth ℂ S)
  (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
  (hdt : KaehlerDifferential.D ℂ S t ∉
    (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
-- imply
  ∃ g : S, σ₀ g ≠ 0 ∧
    let _ : Algebra ℂ[X] (Localization.Away g) :=
      ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
    Algebra.IsStandardEtale ℂ[X] (Localization.Away g) := by
-- proof
  classical
  let _ := hsm
  let _ : Algebra ℂ[X] S := (Polynomial.aeval t).toRingHom.toAlgebra
  have halg : ∀ p : ℂ[X], algebraMap ℂ[X] S p = Polynomial.aeval t p := fun _ => rfl
  let _ : IsScalarTower ℂ ℂ[X] S := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, Polynomial.algebraMap_eq, Polynomial.aeval_C])
  have hX : algebraMap ℂ[X] S X = t := by
    rw [halg, Polynomial.aeval_X]
  let _ : Algebra.FiniteType ℂ[X] S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ ℂ[X] S
  let _ : Algebra.FinitePresentation ℂ[X] S :=
    (Algebra.FinitePresentation.of_finiteType (R := ℂ[X]) (A := S)).mp inferInstance
  set 𝔪 : Ideal S := RingHom.ker σ₀.toRingHom with h𝔪
  let h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪]
    apply RingHom.ker_isMaximal_of_surjective σ₀.toRingHom (fun c => ⟨algebraMap ℂ S c, σ₀.commutes c⟩)
  have h1 : Module.rankAtStalk (Ω[S⁄ℂ]) ⟨𝔪, inferInstance⟩ = 1 :=
    rankAtStalk_eq_one (M := Ω[S⁄ℂ]) (p := ⟨𝔪, inferInstance⟩) hrank
  have hψ := bijective_smul_mk (𝔪 := 𝔪) (x := KaehlerDifferential.D ℂ S t) h1 (by rw [h𝔪]; apply hdt)
  have hEt : Algebra.IsEtaleAt ℂ[X] 𝔪 := by
    have : (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus ℂ[X] S := by
      rw [Algebra.etaleLocus_eq_compl_support]
      refine ⟨notMem_support_kaehlerDifferential (t := t) (𝔪 := 𝔪) hX hψ.2,
        notMem_support_h1Cotangent (t := t) (𝔪 := 𝔪) hX hψ.1⟩
    apply Algebra.mem_etaleLocus_iff.1 this
  obtain ⟨g, hg𝔪, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := ℂ[X]) 𝔪
  refine ⟨g, fun h0 => hg𝔪 (by rw [h𝔪, RingHom.mem_ker]; apply h0), ?_⟩
  have hinst : (((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra :
      Algebra ℂ[X] (Localization.Away g)) = (inferInstance : Algebra ℂ[X] (Localization.Away g)) := by
    refine Algebra.algebra_ext _ _ (fun p => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply ℂ[X] S (Localization.Away g), halg]
    rfl
  rw [hinst]
  apply hSE


-- created on 2026-10-16
