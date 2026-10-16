import Mathlib
import sympy.Basic
open Topology Filter Metric


private lemma rankAtStalk_bot
  {R : Type u} [CommRing R] [IsDomain R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M]
-- given
  (h0 : Module.rank R M = 1) :
-- imply
  Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) = 1 := by
-- proof
  have hp : (⊥ : Ideal R).primeCompl ≤ nonZeroDivisors R := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    simpa [Ideal.primeCompl] using hx
  unfold Module.rankAtStalk
  apply Module.finrank_eq_of_rank_eq
  rw [IsLocalization.rank_eq (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl hp,
    IsLocalizedModule.rank_eq (⊥ : Ideal R).primeCompl hp
      (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl M), h0]
  simp

private lemma rankAtStalk_eq_one
  {R : Type u} [CommRing R] [IsDomain R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M]
-- given
  (h0 : Module.rank R M = 1)
  (p : PrimeSpectrum R) :
-- imply
  Module.rankAtStalk M p = 1 := by
-- proof
  have : PreconnectedSpace (PrimeSpectrum R) :=
    ⟨(IrreducibleSpace.isIrreducible_univ (PrimeSpectrum R)).2.isPreconnected⟩
  rw [Module.isLocallyConstant_rankAtStalk.apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  apply rankAtStalk_bot h0

private lemma exists_generator_mod
  {R : Type u} [CommRing R] [IsDomain R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M]
-- given
  (h0 : Module.rank R M = 1)
  (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] :
-- imply
  ∃ m₀ : M, ∀ m : M, m ∈ Submodule.span R {m₀} ⊔ 𝔪 • (⊤ : Submodule R M) := by
-- proof
  classical
  let p : PrimeSpectrum R := ⟨𝔪, h𝔪.isPrime⟩
  have hfree : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) := by
    have := (Module.freeLocus_eq_univ (R := R) (M := M)).symm ▸ Set.mem_univ p
    apply Module.mem_freeLocus.mp this
  have hrk : Module.finrank (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M) = 1 :=
    rankAtStalk_eq_one h0 p
  let b := Module.Free.chooseBasis (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl M)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (Localization.AtPrime 𝔪)
      (LocalizedModule 𝔪.primeCompl M)) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrk]
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have hgen : ∀ x : LocalizedModule 𝔪.primeCompl M, ∃ c : Localization.AtPrime 𝔪, x = c • b i₀ := by
    intro x
    refine ⟨b.repr x i₀, ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    rw [Fintype.sum_eq_single i₀ (fun j hj => absurd (hi₀ j) hj)]
  obtain ⟨⟨m₀, s₀⟩, hms⟩ : ∃ ms : M × 𝔪.primeCompl, LocalizedModule.mk ms.1 ms.2 = b i₀ := by
    induction b i₀ using LocalizedModule.induction_on with
    | h m s =>
      exact ⟨⟨m, s⟩, rfl⟩
  refine ⟨m₀, fun m => ?_⟩
  obtain ⟨c, hc⟩ := hgen (LocalizedModule.mk m 1)
  obtain ⟨r, u, rfl⟩ : ∃ (r : R) (u : 𝔪.primeCompl), c = Localization.mk r u := by
    induction c using Localization.induction_on with
    | H y =>
      exact ⟨y.1, y.2, rfl⟩
  rw [← hms, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq] at hc
  obtain ⟨v, hv⟩ := hc
  have hv' : ((v : R) * (u * s₀ : 𝔪.primeCompl)) • m = ((v : R) * r) • m₀ := by
    simpa [Submonoid.smul_def, smul_smul, mul_assoc] using hv
  set w : R := (v : R) * (u * s₀ : 𝔪.primeCompl) with hw
  have hwn : w ∉ 𝔪 := (𝔪.primeCompl.mul_mem v.2 (u * s₀).2)
  obtain ⟨y, i, hi, hyi⟩ := h𝔪.exists_inv hwn
  have hm : m = (y * ((v : R) * r)) • m₀ + i • m := calc
    _ = (y * w + i) • m := by rw [hyi, one_smul]
      _ = y • (w • m) + i • m := by rw [add_smul, mul_smul]
      _ = y • (((v : R) * r) • m₀) + i • m := by rw [hw, hv']
      _ = (y * ((v : R) * r)) • m₀ + i • m := by rw [← mul_smul]
  rw [hm]
  apply Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m₀))
    (Submodule.smul_mem_smul hi Submodule.mem_top)


/--
[Algebra_ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_ker_smul_top_sup_span_kaehlerDifferentialD_eq_top_of_bijOn_of_differentiableOn.lean)
-/
@[path]
private lemma main
  {Sc : Type} [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
-- given
  (hSc : Algebra.Smooth ℂ Sc)
  (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
  {t : Sc} {σ₀ : Sc →ₐ[ℂ] ℂ} {r : ℝ} {𝒰 : Set (Sc →ₐ[ℂ] ℂ)}
  (_ : 0 < r)
  (_ : σ₀ ∈ 𝒰)
  (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
  (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧
    ∀ σ ∈ 𝒰, σ s = F (σ t)) :
-- imply
  ∀ σ ∈ 𝒰, (RingHom.ker σ.toRingHom) • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ⊔
    Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} = ⊤ := by
-- proof
  intro σ₁ hσ₁
  classical
  have : Algebra.FormallySmooth ℂ Sc := hSc.formallySmooth
  have : IsNoetherianRing Sc := Algebra.FiniteType.isNoetherianRing ℂ Sc
  have : Module.Finite Sc (KaehlerDifferential ℂ Sc) := inferInstance
  have : Module.FinitePresentation Sc (KaehlerDifferential ℂ Sc) :=
    Module.finitePresentation_of_projective _ _
  set 𝔪 : Ideal Sc := RingHom.ker σ₁.toRingHom with h𝔪def
  have h𝔪 : 𝔪.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective σ₁.toRingHom (fun c => ⟨algebraMap ℂ Sc c, σ₁.commutes c⟩)
  obtain ⟨m₀, hm₀⟩ := exists_generator_mod (R := Sc) (M := KaehlerDifferential ℂ Sc) hΩ 𝔪
  set z₁ : ℂ := σ₁ t with hz₁def
  have hz₁ : z₁ ∈ Metric.ball (σ₀ t) r := hbij.mapsTo hσ₁
  have hnhds : Metric.ball (σ₀ t) r ∈ 𝓝 z₁ := Metric.isOpen_ball.mem_nhds hz₁
  choose F hF using hhol
  have hFd : ∀ s, DifferentiableAt ℂ (F s) z₁ := fun s => (hF s).1.differentiableAt hnhds
  have hFval : ∀ s, F s z₁ = σ₁ s := fun s => ((hF s).2 σ₁ hσ₁).symm
  have honball : ∀ {g g' : ℂ → ℂ}, (∀ σ ∈ 𝒰, g (σ t) = g' (σ t)) → g =ᶠ[𝓝 z₁] g' := by
    intro g g' h
    refine Filter.eventuallyEq_of_mem hnhds (fun z hz => ?_)
    obtain ⟨σ, hσ, rfl⟩ := hbij.surjOn hz
    apply h σ hσ
  set d : Sc → ℂ := fun s => deriv (F s) z₁ with hddef
  have hd_mul : ∀ a b : Sc, d (a * b) = σ₁ a * d b + σ₁ b * d a := by
    intro a b
    have heq : F (a * b) =ᶠ[𝓝 z₁] (fun z => F a z * F b z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, ← (hF b).2 σ hσ, map_mul])
    show deriv (F (a * b)) z₁ = _
    rw [heq.deriv_eq, deriv_fun_mul (hFd a) (hFd b), hFval, hFval]
    ring
  have hd_add : ∀ a b : Sc, d (a + b) = d a + d b := by
    intro a b
    have heq : F (a + b) =ᶠ[𝓝 z₁] (fun z => F a z + F b z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, ← (hF b).2 σ hσ, map_add])
    show deriv (F (a + b)) z₁ = _
    rw [heq.deriv_eq, deriv_fun_add (hFd a) (hFd b)]
  have hd_smul : ∀ (c : ℂ) (a : Sc), d (c • a) = c * d a := by
    intro c a
    have heq : F (c • a) =ᶠ[𝓝 z₁] (fun z => c * F a z) :=
      honball (fun σ hσ => by rw [← (hF _).2 σ hσ, ← (hF a).2 σ hσ, map_smul, smul_eq_mul])
    show deriv (F (c • a)) z₁ = _
    rw [heq.deriv_eq, deriv_const_mul c (hFd a)]
  have hd_t : d t = 1 := by
    have heq : F t =ᶠ[𝓝 z₁] (fun z => z) := honball (fun σ hσ => by rw [← (hF t).2 σ hσ])
    show deriv (F t) z₁ = 1
    rw [heq.deriv_eq, deriv_id'']
  set ι : ℂ →+* Sc ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp (algebraMap ℂ Sc) with hιdef
  have hmk : ∀ s : Sc, Ideal.Quotient.mk 𝔪 s = ι (σ₁ s) := by
    intro s
    show Ideal.Quotient.mk 𝔪 s = Ideal.Quotient.mk 𝔪 (algebraMap ℂ Sc (σ₁ s))
    rw [Ideal.Quotient.eq]
    show s - algebraMap ℂ Sc (σ₁ s) ∈ RingHom.ker σ₁.toRingHom
    rw [RingHom.mem_ker]
    simp
  have hsmulC : ∀ (c : ℂ) (q : Sc ⧸ 𝔪), c • q = ι c * q := by
    intro c q
    rw [Algebra.smul_def]
    congr 1
  have hsmulS : ∀ (a : Sc) (q : Sc ⧸ 𝔪), a • q = Ideal.Quotient.mk 𝔪 a * q := by
    intro a q
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  let Dpt : Derivation ℂ Sc (Sc ⧸ 𝔪) :=
    { toFun := fun s => ι (d s)
      map_add' := by
        intro a b
        simp only [hd_add, map_add]
      map_smul' := by
        intro c a
        simp only [hd_smul, map_mul, RingHom.id_apply, hsmulC]
      map_one_eq_zero' := by
        show ι (d 1) = 0
        have h : d 1 = d 1 + d 1 := by simpa using hd_mul 1 1
        have : d 1 = 0 := by linear_combination -h
        rw [this, map_zero]
      leibniz' := by
        intro a b
        show ι (d (a * b)) = a • ι (d b) + b • ι (d a)
        rw [hsmulS, hsmulS, hmk a, hmk b, hd_mul, map_add, map_mul, map_mul] }
  set lam : KaehlerDifferential ℂ Sc →ₗ[Sc] Sc ⧸ 𝔪 := Dpt.liftKaehlerDifferential with hlamdef
  have hlam_t : lam (KaehlerDifferential.D ℂ Sc t) = 1 := by
    rw [hlamdef, Derivation.liftKaehlerDifferential_comp_D]
    show ι (d t) = 1
    rw [hd_t, map_one]
  have hlam_smul : ∀ n ∈ 𝔪 • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)), lam n = 0 := by
    intro n hn
    refine Submodule.smul_induction_on hn (fun a ha ω _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, hsmulS, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    · rw [map_add, hx, hy, add_zero]
  obtain ⟨y, hy, n, hn, hsum⟩ := Submodule.mem_sup.mp (hm₀ (KaehlerDifferential.D ℂ Sc t))
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hkey : Ideal.Quotient.mk 𝔪 a * lam m₀ = 1 := by
    have := congrArg lam hsum
    rwa [map_add, map_smul, hsmulS, hlam_smul n hn, add_zero, hlam_t] at this
  have ha : a ∉ 𝔪 := by
    intro ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul] at hkey
    exact zero_ne_one hkey
  obtain ⟨yv, i, hi, hyi⟩ := h𝔪.exists_inv ha
  have hm₀mem : m₀ ∈ Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} ⊔
    𝔪 • (⊤ : Submodule Sc _) := by
    have hm : m₀ = yv • (KaehlerDifferential.D ℂ Sc t - n) + i • m₀ := by
      have h1 : a • m₀ = KaehlerDifferential.D ℂ Sc t - n := by
        rw [← hsum]
        abel
      calc
        _ = (yv * a + i) • m₀ := by rw [hyi, one_smul]
        _ = yv • (a • m₀) + i • m₀ := by rw [add_smul, mul_smul]
        _ = yv • (KaehlerDifferential.D ℂ Sc t - n) + i • m₀ := by rw [h1]
    rw [hm]
    refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (Submodule.smul_mem_smul hi Submodule.mem_top))
    rw [smul_sub]
    apply Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hn))
  have hle : Submodule.span Sc {m₀} ⊔ 𝔪 • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) ≤
      Submodule.span Sc {KaehlerDifferential.D ℂ Sc t} ⊔
        𝔪 • (⊤ : Submodule Sc (KaehlerDifferential ℂ Sc)) :=
    sup_le (by rwa [Submodule.span_singleton_le_iff_mem]) le_sup_right
  rw [eq_top_iff, sup_comm]
  intro ω _
  apply hle (hm₀ ω)


-- created on 2026-10-16
