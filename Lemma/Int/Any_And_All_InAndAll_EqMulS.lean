import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w x

private lemma isPrincipalIdealRing_integralClosure {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (K₀ : Type v) [Field K₀] [Algebra C K₀] [IsFractionRing C K₀] {κ : Type w} [Field κ] [Algebra K₀ κ] [Algebra C κ] [IsScalarTower C K₀ κ] [FiniteDimensional K₀ κ] [Algebra.IsSeparable K₀ κ] : IsPrincipalIdealRing (integralClosure C κ) := by
  set B := integralClosure C κ
  let _ : IsDedekindDomain B := integralClosure.isDedekindDomain C K₀ κ
  let _ : Module.Finite C B := IsIntegralClosure.finite C K₀ κ B
  let _ : Module.IsTorsionFree C κ := .trans_faithfulSMul C K₀ κ
  let _ : Module.IsTorsionFree C B := IsIntegralClosure.isTorsionFree C κ
  have hp0 : IsLocalRing.maximalIdeal C ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField C (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid B (IsLocalRing.maximalIdeal C).primeCompl) B := by
    apply IsLocalization.of_le_isUnit
    intro _ hx
    obtain ⟨c, hc, rfl⟩ := hx
    suffices hcu : IsUnit c from hcu.map _
    by_contra h
    exact hc ((IsLocalRing.mem_maximalIdeal c).mpr h)
  exact IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (R := C) B (IsLocalRing.maximalIdeal C) hp0 (Sₚ := B)

private lemma exists_subalgebra_finite_locallyPrincipal {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (K₀ : Type v) [Field K₀] [Algebra C K₀] [IsFractionRing C K₀] {κ : Type w} [Field κ] [Algebra K₀ κ] [Algebra C κ] [IsScalarTower C K₀ κ] [FiniteDimensional K₀ κ] [Algebra.IsSeparable K₀ κ] {A : Type x} [CommRing A] [Algebra C A] [Algebra A κ] [IsScalarTower C A κ] : ∃ D₁ : Subalgebra A κ, Module.Finite A D₁ ∧ (∀ x : κ, IsIntegral C x → x ∈ D₁) ∧ ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y := by
  classical
  set B := integralClosure C κ
  let _ : IsDedekindDomain B := integralClosure.isDedekindDomain C K₀ κ
  let _ : Module.Finite C B := IsIntegralClosure.finite C K₀ κ B
  let _ : IsPrincipalIdealRing B := isPrincipalIdealRing_integralClosure K₀
  obtain ⟨S, hS⟩ := Module.finite_def.mp (inferInstance : Module.Finite C B)
  set S' : Set κ := ((↑) : B → κ) '' (S : Set B)
  set D₁ : Subalgebra A κ := Algebra.adjoin A S'
  have hS'fin : S'.Finite := (S.finite_toSet).image _
  have hS'int : ∀ x ∈ S', IsIntegral A x := by
    intro _ hx
    obtain ⟨b, -, rfl⟩ := hx
    exact IsIntegral.tower_top (A := A) (b.2 : IsIntegral C (b : κ))
  have hfin : Module.Finite A D₁ := Algebra.finite_adjoin_of_finite_of_isIntegral hS'fin hS'int
  have hBD : ∀ b : B, (b : κ) ∈ D₁ := by
    intro b
    have hb : b ∈ Submodule.span C (S : Set B) := by
      rw [hS]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    ·
      intro s hs
      exact Algebra.subset_adjoin ⟨s, hs, rfl⟩
    ·
      rw [ZeroMemClass.coe_zero]
      refine D₁.zero_mem
    ·
      intro x y _ _ hx hy
      rw [Subalgebra.coe_add]
      refine D₁.add_mem hx hy
    ·
      intro c x _ hx
      have : ((c • x : B) : κ) = algebraMap A κ (algebraMap C A c) * (x : κ) := by
        rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply C A κ]
      rw [this]
      refine D₁.mul_mem (D₁.algebraMap_mem _) hx
  have hint : ∀ x : κ, IsIntegral C x → x ∈ D₁ := fun x hx => hBD ⟨x, hx⟩
  refine ⟨D₁, hfin, hint, ?_⟩
  set incl : B →+* D₁ :=
    { toFun := fun b => ⟨b, hBD b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hincl_coe : ∀ b : B, ((incl b : D₁) : κ) = (b : κ) := fun b => rfl
  intro 𝔫 h𝔫
  if hbot : 𝔫 = ⊥ then
    refine ⟨0, 𝔫.zero_mem, fun x hx => ⟨1, ?_, 0, ?_⟩⟩
    ·
      rw [hbot]
      simp only [Ideal.mem_bot, one_ne_zero, not_false_eq_true]
    ·
      rw [hbot, Ideal.mem_bot] at hx
      rw [hx, mul_zero, mul_zero]
  else
    set 𝔮 : Ideal B := 𝔫.comap incl
    let _ : 𝔮.IsPrime := Ideal.comap_isPrime incl 𝔫
    have hfrac : ∀ z : κ, ∃ b : B, ∃ c : C, c ≠ 0 ∧ z * algebraMap C κ c = b := by
      intro z
      have hz : IsAlgebraic C z := (IsFractionRing.isAlgebraic_iff C K₀ κ).mpr (Algebra.IsAlgebraic.isAlgebraic (R := K₀) z)
      obtain ⟨c, hc0, hcz⟩ := hz.exists_integral_multiple
      refine ⟨⟨c • z, hcz⟩, c, hc0, ?_⟩
      rw [Subtype.coe_mk, Algebra.smul_def, mul_comm]
    have hCinj : Function.Injective (algebraMap C κ) := by
      rw [IsScalarTower.algebraMap_eq C K₀ κ]
      exact (algebraMap K₀ κ).injective.comp (IsFractionRing.injective C K₀)
    have h𝔮0 : 𝔮 ≠ ⊥ := by
      intro h0
      apply hbot
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨b, c, hc0, hbc⟩ := hfrac (x : κ)
      have hmemc : algebraMap C κ c ∈ D₁ := by
        rw [IsScalarTower.algebraMap_apply C A κ]
        refine D₁.algebraMap_mem _
      have hbmem : incl b ∈ 𝔫 := by
        have : incl b = x * ⟨algebraMap C κ c, hmemc⟩ := by
          apply Subtype.ext
          rw [hincl_coe, ← hbc]
          rfl
        rw [this]
        exact 𝔫.mul_mem_right _ hx
      have hb0 : b = 0 := by
        have : b ∈ 𝔮 := hbmem
        rwa [h0, Ideal.mem_bot] at this
      rw [hb0, ZeroMemClass.coe_zero, mul_eq_zero] at hbc
      obtain h | h := hbc
      · exact Ideal.mem_bot.mpr (Subtype.ext h)
      · exact absurd h ((map_ne_zero_iff _ hCinj).mpr hc0)
    set t₀ : B := Submodule.IsPrincipal.generator 𝔮
    have h𝔮span : 𝔮 = Ideal.span {t₀} := (Ideal.span_singleton_generator 𝔮).symm
    have ht₀0 : t₀ ≠ 0 := by
      intro h
      apply h𝔮0
      rw [h𝔮span, h, Ideal.span_singleton_eq_bot]
    have ht₀prime : Prime t₀ := (Ideal.span_singleton_prime ht₀0).mp (h𝔮span ▸ inferInstance)
    have ht₀irr : Irreducible t₀ := ht₀prime.irreducible
    have ht₀𝔫 : incl t₀ ∈ 𝔫 := by
      show t₀ ∈ 𝔮
      rw [h𝔮span]
      refine Ideal.mem_span_singleton_self t₀
    have key : ∀ d : D₁, ∃ a a' : B, ¬ t₀ ∣ a' ∧ (d : κ) * a' = a := by
      intro d
      obtain ⟨b, c, hc0, hbc⟩ := hfrac (d : κ)
      set cB : B := algebraMap C B c
      have hcBκ : (cB : κ) = algebraMap C κ c := (IsScalarTower.algebraMap_apply C B κ c).symm
      have hcB0 : cB ≠ 0 := by
        intro h
        apply hc0
        apply hCinj
        rw [← hcBκ, h, map_zero]
        rfl
      if hb0 : b = 0 then
        refine ⟨0, 1, ht₀irr.not_isUnit ∘ isUnit_of_dvd_one, ?_⟩
        have hd0 : (d : κ) = 0 := by
          rw [hb0, ZeroMemClass.coe_zero, mul_eq_zero] at hbc
          obtain h | h := hbc
          · exact h
          · exact absurd h ((map_ne_zero_iff _ hCinj).mpr hc0)
        rw [hd0, zero_mul, ZeroMemClass.coe_zero]
      else
        obtain ⟨i, b₀, hb₀, rfl⟩ := WfDvdMonoid.max_power_factor hb0 ht₀irr
        obtain ⟨j, c₀, hc₀, hcfac⟩ := WfDvdMonoid.max_power_factor hcB0 ht₀irr
        have ht₀κ : (t₀ : κ) ≠ 0 := fun h => ht₀0 (Subtype.ext h)
        have hrel : (d : κ) * (c₀ : κ) * (t₀ : κ) ^ j = (t₀ : κ) ^ i * (b₀ : κ) := by
          have h1 : (d : κ) * (cB : κ) = ((t₀ ^ i * b₀ : B) : κ) := by rw [hcBκ, hbc]
          rw [hcfac] at h1
          push_cast at h1
          linear_combination h1
        if hij : j ≤ i then
          refine ⟨t₀ ^ (i - j) * b₀, c₀, hc₀, ?_⟩
          push_cast
          have : (t₀ : κ) ^ i = (t₀ : κ) ^ (i - j) * (t₀ : κ) ^ j := by
            rw [← pow_add, Nat.sub_add_cancel hij]
          rw [this] at hrel
          refine mul_right_cancel₀ (pow_ne_zero j ht₀κ) ?_
          rw [hrel]
          ring
        else
          exfalso
          push Not at hij
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hij
          have hz : (t₀ : κ) ^ i * ((b₀ : κ) - (t₀ : κ) * ((t₀ : κ) ^ k * (c₀ : κ) * (d : κ))) = 0 := by
            rw [hk] at hrel
            linear_combination (-1 : κ) * hrel
          have hi0 : (t₀ : κ) ^ i ≠ 0 := pow_ne_zero _ ht₀κ
          have hb₀eq : (b₀ : κ) = (t₀ : κ) * ((t₀ : κ) ^ k * (c₀ : κ) * (d : κ)) := by
            have := (mul_eq_zero.mp hz).resolve_left hi0
            linear_combination this
          have hmem : incl b₀ ∈ 𝔫 := by
            have : incl b₀ = incl t₀ * (incl (t₀ ^ k * c₀) * d) := by
              apply Subtype.ext
              simp only [Subalgebra.coe_mul, hincl_coe]
              push_cast
              rw [hb₀eq]
            rw [this]
            refine 𝔫.mul_mem_right _ ht₀𝔫
          have : b₀ ∈ 𝔮 := hmem
          rw [h𝔮span, Ideal.mem_span_singleton] at this
          exact hb₀ this
    refine ⟨incl t₀, ht₀𝔫, fun x hx => ?_⟩
    obtain ⟨a, a', ha', hxa⟩ := key x
    have hamem : incl a ∈ 𝔫 := by
      have : incl a = x * incl a' := by
        apply Subtype.ext
        rw [hincl_coe, Subalgebra.coe_mul, hincl_coe, hxa]
      rw [this]
      refine 𝔫.mul_mem_right _ hx
    have ha𝔮 : a ∈ 𝔮 := hamem
    rw [h𝔮span, Ideal.mem_span_singleton] at ha𝔮
    obtain ⟨y₀, rfl⟩ := ha𝔮
    refine ⟨incl a', fun h => ha' ?_, incl y₀, ?_⟩
    ·
      have : a' ∈ 𝔮 := h
      rwa [h𝔮span, Ideal.mem_span_singleton] at this
    ·
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hincl_coe, hincl_coe, hincl_coe, mul_comm, hxa]
      push_cast
      ring

/--
[IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring.lean)
-/
@[path]
private lemma main
  {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  (K₀ : Type v) [Field K₀] [Algebra C K₀] [IsFractionRing C K₀]
  {κ : Type w} [Field κ] [Algebra K₀ κ] [Algebra C κ] [IsScalarTower C K₀ κ] [FiniteDimensional K₀ κ] [Algebra.IsSeparable K₀ κ]
  {A : Type x} [CommRing A] [Algebra C A] [Algebra A κ] [IsScalarTower C A κ] :
  -- imply
  ∃ D₁ : Subalgebra A κ, Module.Finite A D₁ ∧ (∀ x : κ, IsIntegral C x → x ∈ D₁) ∧ ∀ 𝔫 : Ideal D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : D₁, s * x = t * y :=
    exists_subalgebra_finite_locallyPrincipal K₀


-- created on 2026-10-20
