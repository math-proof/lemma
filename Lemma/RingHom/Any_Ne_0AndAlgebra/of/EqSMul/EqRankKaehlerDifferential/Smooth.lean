import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct nonZeroDivisors


private lemma rankAtStalk_eq
  {S : Type} [CommRing S] [IsDomain S]
  {M : Type} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M] [Module.Flat S M]
  {n : ℕ}
-- given
  (hrank : Module.rank S M = n)
  (p : PrimeSpectrum S) :
-- imply
  Module.rankAtStalk M p = n := by
-- proof
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply hx
    rw [h0]
    apply Submodule.zero_mem
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal S).primeCompl) (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl)
        (f := LocalizedModule.mkLinearMap (⊥ : Ideal S).primeCompl M) (hp := hle), hrank]
  show Module.finrank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n
  apply Module.finrank_eq_of_rank_eq (by rw [hr])

private lemma exists_smul_mem_of_mk_mem
  {S : Type} [CommRing S]
  {M : Type} [AddCommGroup M] [Module S M]
  {𝔭 : Ideal S} [𝔭.IsPrime]
  {N : Submodule S M} {x : M}
-- given
  (h : LocalizedModule.mk x (1 : 𝔭.primeCompl) ∈
    N.localized' (Localization.AtPrime 𝔭) 𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl M)) :
-- imply
  ∃ r : S, r ∉ 𝔭 ∧ r • x ∈ N := by
-- proof
  rw [Submodule.mem_localized', IsLocalizedModule.mk_eq_mk'] at h
  obtain ⟨m, hm, s, hms⟩ := h
  rw [IsLocalizedModule.mk'_eq_mk'_iff] at hms
  obtain ⟨c, hc⟩ := hms
  have hcx : ((c : S) * (s : S)) • x = (c : S) • m := by
    have := hc
    simp only [one_smul, Submonoid.smul_def, smul_smul] at this
    apply this
  refine ⟨(c : S) * (s : S), ‹𝔭.IsPrime›.mul_notMem c.2 s.2, ?_⟩
  rw [hcx]
  apply N.smul_mem _ hm

private lemma localized'_sup
  {S : Type} [CommRing S]
  {M N : Type} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  {T : Type} {p : Submonoid S} [CommRing T] [Algebra S T] [IsLocalization p T] [Module T N] [IsScalarTower S T N]
  (f : M →ₗ[S] N) [IsLocalizedModule p f]
  (A B : Submodule S M) :
-- imply
  (A ⊔ B).localized' T p f = A.localized' T p f ⊔ B.localized' T p f :=
  (Submodule.localized'gi T p f).gc.l_sup

private lemma bijective_linearCombination
  {S : Type} [CommRing S]
  {M : Type} [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Flat S M]
  {𝔪 : Ideal S} [𝔪.IsMaximal]
  {n : ℕ}
-- given
  (x : Fin n → M)
  (hn : Module.rankAtStalk M ⟨𝔪, inferInstance⟩ = n)
  (hx : 𝔪 • (⊤ : Submodule S M) ⊔ Submodule.span S (Set.range x) = ⊤) :
-- imply
  Function.Bijective (Fintype.linearCombination (Localization.AtPrime 𝔪)
    (fun i => LocalizedModule.mk (x i) (1 : 𝔪.primeCompl))) := by
-- proof
  set ω : Fin n → LocalizedModule 𝔪.primeCompl M := fun i => LocalizedModule.mk (x i) (1 : 𝔪.primeCompl) with hω
  set ψ := Fintype.linearCombination (Localization.AtPrime 𝔪) ω with hψ
  have hn' : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = n := hn
  have hloc := congrArg (Submodule.localized' (Localization.AtPrime 𝔪) 𝔪.primeCompl
    (LocalizedModule.mkLinearMap 𝔪.primeCompl M)) hx
  rw [localized'_sup, Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
    Localization.AtPrime.map_eq_maximalIdeal, Submodule.localized'_span, ← Set.range_comp] at hloc
  have hrange : (LocalizedModule.mkLinearMap 𝔪.primeCompl M) ∘ x = ω := by
    funext i
    rfl
  rw [hrange] at hloc
  have hspan : Submodule.span (Localization.AtPrime 𝔪) (Set.range ω) = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot (N' := ⊤) Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_)
    rw [sup_comm, hloc]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, hψ, Fintype.range_linearCombination, hspan]
  let _ : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) hn'
  have hcomp : Function.Surjective (b.equivFun.toLinearMap.comp ψ) :=
    b.equivFun.surjective.comp hsurj
  have hinj : Function.Injective (b.equivFun.toLinearMap.comp ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hcomp
  have hinj' : Function.Injective (⇑b.equivFun ∘ ⇑ψ) := by
    rw [LinearMap.coe_comp, LinearEquiv.coe_coe] at hinj
    apply hinj
  refine ⟨Function.Injective.of_comp hinj', hsurj⟩

private lemma D_algebraMap_eq_zero
  {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (r : R) :
-- imply
  KaehlerDifferential.D R A (algebraMap R A r) = 0 := by
-- proof
  rw [Algebra.algebraMap_eq_smul_one, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]

private lemma notMem_support_kaehlerDifferential
  {S : Type} [CommRing S]
  {R : Type} [CommRing R] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S]
  {n : ℕ} {t : Fin n → S}
-- given
  (ht : ∀ i, ∃ r : R, algebraMap R S r = t i)
  {𝔪 : Ideal S} [𝔪.IsMaximal]
  (hspan : Submodule.span (Localization.AtPrime 𝔪)
    (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) = ⊤) :
-- imply
  (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S (Ω[S⁄R]) := by
-- proof
  rw [Module.notMem_support_iff']
  intro m
  obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective ℂ R S m
  have hmem : LocalizedModule.mk ω₁ (1 : 𝔪.primeCompl) ∈
    (Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i))).localized'
      (Localization.AtPrime 𝔪) 𝔪.primeCompl (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) := by
    rw [Submodule.localized'_span, ← Set.range_comp]
    have : (LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ])) ∘ (fun i => KaehlerDifferential.D ℂ S (t i)) =
        fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) := by
      funext i
      rfl
    rw [this, hspan]
    apply Submodule.mem_top
  obtain ⟨r, hr, hrω⟩ := exists_smul_mem_of_mk_mem hmem
  refine ⟨r, hr, ?_⟩
  rw [← LinearMap.map_smul]
  apply (show Submodule.span S (Set.range fun i => KaehlerDifferential.D ℂ S (t i)) ≤ LinearMap.ker (KaehlerDifferential.map ℂ R S S) from Submodule.span_le.mpr (by intro _ h; obtain ⟨i, rfl⟩ := h; obtain ⟨ri, hri⟩ := ht i; show KaehlerDifferential.D ℂ S (t i) ∈ LinearMap.ker (KaehlerDifferential.map ℂ R S S); rw [LinearMap.mem_ker, KaehlerDifferential.map_D, Algebra.algebraMap_self_apply, ← hri, D_algebraMap_eq_zero])) hrω

private lemma notMem_support_h1Cotangent
  {S : Type} [CommRing S] [Algebra ℂ S] [Algebra.FormallySmooth ℂ S]
  {n : ℕ} [Algebra (MvPolynomial (Fin n) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S]
  {t : Fin n → S}
-- given
  (hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i)
  {𝔪 : Ideal S} [𝔪.IsMaximal]
  (hψ : Function.Injective (Fintype.linearCombination (Localization.AtPrime 𝔪)
    (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)))) :
-- imply
  (⟨𝔪, Ideal.IsMaximal.isPrime inferInstance⟩ : PrimeSpectrum S) ∉
    Module.support S (Algebra.H1Cotangent (MvPolynomial (Fin n) ℂ) S) := by
-- proof
  classical
  set R := MvPolynomial (Fin n) ℂ with hR
  rw [Module.notMem_support_iff']
  intro h
  have hinj : Function.Injective (Algebra.H1Cotangent.δ ℂ R S) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ (R := ℂ) (S := R) (T := S) z).1 hz
    rw [Subsingleton.elim w 0, LinearMap.map_zero]
  have hδ0 : KaehlerDifferential.mapBaseChange ℂ R S (Algebra.H1Cotangent.δ ℂ R S h) = 0 :=
    (Algebra.H1Cotangent.exact_δ_mapBaseChange (R := ℂ) (S := R) (T := S) _).2 ⟨h, rfl⟩
  let B : Module.Basis (Fin n) S (S ⊗[R] Ω[R⁄ℂ]) :=
    Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n))
  have hB : ∀ i, B i = (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (MvPolynomial.X i) := by
    intro i
    rw [show B i = Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n)) i from rfl,
      Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  set a : Fin n → S := fun i => B.repr (Algebra.H1Cotangent.δ ℂ R S h) i with ha
  have hsum : Algebra.H1Cotangent.δ ℂ R S h = ∑ i, a i • B i := (B.sum_repr _).symm
  have hmap : ∀ i, KaehlerDifferential.mapBaseChange ℂ R S (B i) = KaehlerDifferential.D ℂ S (t i) := by
    intro i
    rw [hB, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, hX, one_smul]
  have hzero : ∑ i, a i • KaehlerDifferential.D ℂ S (t i) = 0 := by
    have := hδ0
    rw [hsum, map_sum] at this
    simp only [map_smul, hmap] at this
    apply this
  have hloc : Fintype.linearCombination (Localization.AtPrime 𝔪)
    (fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl))
    (fun i => algebraMap S (Localization.AtPrime 𝔪) (a i)) = 0 := by
    rw [Fintype.linearCombination_apply]
    have : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) •
        LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl) =
        LocalizedModule.mkLinearMap 𝔪.primeCompl (Ω[S⁄ℂ]) (a i • KaehlerDifferential.D ℂ S (t i)) := by
      intro i
      rw [algebraMap_smul, LinearMap.map_smul]
      rfl
    simp only [this, ← map_sum, hzero, map_zero]
  have hai : ∀ i, algebraMap S (Localization.AtPrime 𝔪) (a i) = 0 := by
    intro i
    have := hψ (hloc.trans (map_zero _).symm)
    apply congrFun this i
  choose c hc using fun i => (IsLocalization.map_eq_zero_iff 𝔪.primeCompl (Localization.AtPrime 𝔪) (a i)).1 (hai i)
  set C : 𝔪.primeCompl := ∏ i, c i with hC
  have hCa : ∀ i, (C : S) * a i = 0 := by
    intro i
    rw [hC, Submonoid.coe_finsetProd, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, hc i, mul_zero]
  refine ⟨C, C.2, hinj ?_⟩
  rw [LinearMap.map_smul, map_zero, hsum, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_smul, hCa i, zero_smul]


/--
[Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
  {n : ℕ} {σ₀ : S →ₐ[ℂ] ℂ} {t : Fin n → S}
-- given
  (hsm : Algebra.Smooth ℂ S)
  (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
  (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
    Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
-- imply
  ∃ g : S, σ₀ g ≠ 0 ∧
    let _ : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
      ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
    Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by
-- proof
  classical
  let _ : Algebra.Smooth ℂ S := hsm
  let _ : Algebra (MvPolynomial (Fin n) ℂ) S := (MvPolynomial.aeval t).toRingHom.toAlgebra
  have halg : ∀ p : MvPolynomial (Fin n) ℂ, algebraMap (MvPolynomial (Fin n) ℂ) S p = MvPolynomial.aeval t p :=
    fun _ => rfl
  let _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C])
  have hX : ∀ i, algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X i) = t i := fun i => by
    rw [halg, MvPolynomial.aeval_X]
  let _ : Algebra.FiniteType (MvPolynomial (Fin n) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (MvPolynomial (Fin n) ℂ) S
  let _ : Algebra.FinitePresentation (MvPolynomial (Fin n) ℂ) S :=
    (Algebra.FinitePresentation.of_finiteType (R := MvPolynomial (Fin n) ℂ) (A := S)).mp inferInstance
  set 𝔪 : Ideal S := RingHom.ker σ₀.toRingHom with h𝔪
  let h𝔪max : 𝔪.IsMaximal := by
    rw [h𝔪]
    apply RingHom.ker_isMaximal_of_surjective σ₀.toRingHom (fun c => ⟨algebraMap ℂ S c, σ₀.commutes c⟩)
  have hn : Module.rankAtStalk (Ω[S⁄ℂ]) ⟨𝔪, inferInstance⟩ = n := rankAtStalk_eq hrank _
  have hψ := bijective_linearCombination (𝔪 := 𝔪) (fun i => KaehlerDifferential.D ℂ S (t i)) hn (by rw [h𝔪]; apply hdt)
  have hspan : Submodule.span (Localization.AtPrime 𝔪)
    (Set.range fun i => LocalizedModule.mk (KaehlerDifferential.D ℂ S (t i)) (1 : 𝔪.primeCompl)) = ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    apply hψ.2
  have hEt : Algebra.IsEtaleAt (MvPolynomial (Fin n) ℂ) 𝔪 := by
    have : (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.etaleLocus (MvPolynomial (Fin n) ℂ) S := by
      rw [Algebra.etaleLocus_eq_compl_support]
      refine ⟨notMem_support_kaehlerDifferential (t := t) (fun i => ⟨MvPolynomial.X i, hX i⟩) (𝔪 := 𝔪) hspan,
        notMem_support_h1Cotangent (t := t) hX (𝔪 := 𝔪) hψ.1⟩
    apply Algebra.mem_etaleLocus_iff.1 this
  obtain ⟨g, hg𝔪, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := MvPolynomial (Fin n) ℂ) 𝔪
  refine ⟨g, fun h0 => hg𝔪 (by rw [h𝔪, RingHom.mem_ker]; apply h0), ?_⟩
  have hinst : (((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra :
      Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) =
      (inferInstance : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g)) := by
    refine Algebra.algebra_ext _ _ (fun p => ?_)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) ℂ) S (Localization.Away g), halg]
    rfl
  rw [hinst]
  apply hSE


-- created on 2026-10-16
