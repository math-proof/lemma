import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private abbrev W {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] (ϖ : A) (k : ℕ) : Submodule A M :=
  LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))

private lemma mem_W {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) {k : ℕ} {v : M} : v ∈ W M ϖ k ↔ ∃ w : M, ϖ ^ k • w = v := by
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]

private lemma pow_smul_mem_W {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) (k : ℕ) (w : M) : ϖ ^ k • w ∈ W M ϖ k :=
  (mem_W ϖ).mpr ⟨w, rfl⟩

private lemma W_anti {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) {k k' : ℕ} (h : k ≤ k') : W M ϖ k' ≤ W M ϖ k := by
  intro v hv
  obtain ⟨w, rfl⟩ := (mem_W ϖ).mp hv
  refine (mem_W ϖ).mpr ⟨ϖ ^ (k' - k) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

private lemma pow_smul_eq_zero {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) (hM : ∀ m : M, ϖ • m = 0 → m = 0) (k : ℕ) (m : M) (h : ϖ ^ k • m = 0) : m = 0 := by
  induction k
  · rwa [pow_zero, one_smul] at h
  ·
    rename_i k ih
    apply ih
    apply hM
    rwa [← mul_smul, ← pow_succ']

private lemma pow_smul_injective {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) (hM : ∀ m : M, ϖ • m = 0 → m = 0) (k : ℕ) : Function.Injective (ϖ ^ k • (LinearMap.id : M →ₗ[A] M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  refine pow_smul_eq_zero ϖ hM k m hm

private abbrev red {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) {k k' : ℕ} (h : k ≤ k') : (M ⧸ W M ϖ k') →ₗ[A] (M ⧸ W M ϖ k) :=
  (W M ϖ k').mapQ (W M ϖ k) LinearMap.id (W_anti ϖ h)

private lemma red_mk {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] (ϖ : A) {k k' : ℕ} (h : k ≤ k') (v : M) : red ϖ h (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

private lemma exists_lift_const {A : Type u} [CommRing A] [IsNoetherianRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N] (ϖ : A) (hN : ∀ n : N, ϖ • n = 0 → n = 0) : ∃ n₀ : ℕ, ∀ (m k : ℕ) (hmk : m + n₀ ≤ k) (g : M →ₗ[A] N ⧸ W N ϖ k), ∃ ψ : M →ₗ[A] N, ∀ v : M, (W N ϖ m).mkQ (ψ v) = red ϖ (le_trans (Nat.le_add_right m n₀) hmk) (g v) := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  set K : Submodule A (Fin n → A) := LinearMap.ker π with hKdef
  let _ : IsNoetherian A ↥K := inferInstance
  let _ : Module.Finite A ↥K := inferInstance
  let resK : ((Fin n → A) →ₗ[A] N) →ₗ[A] (↥K →ₗ[A] N) := LinearMap.lcomp A N K.subtype
  have resK_apply : ∀ (f : (Fin n → A) →ₗ[A] N) (κ : ↥K), resK f κ = f κ := fun f κ => rfl
  let R₀ : Submodule A (↥K →ₗ[A] N) := LinearMap.range resK
  obtain ⟨j, πK, hπK⟩ := Module.Finite.exists_fin' A ↥K
  let _ : IsNoetherian A ((Fin j → A) →ₗ[A] N) := inferInstance
  let _ : IsNoetherian A (↥K →ₗ[A] N) := by
    refine isNoetherian_of_injective (LinearMap.lcomp A N πK) fun h h' hh => ?_
    apply LinearMap.ext
    intro κ
    obtain ⟨y, rfl⟩ := hπK κ
    refine LinearMap.congr_fun hh y
  let _ : IsNoetherian A ((↥K →ₗ[A] N) ⧸ R₀) := inferInstance
  let c : OrderHom ℕ (Submodule A ((↥K →ₗ[A] N) ⧸ R₀)) :=
    { toFun := fun i => LinearMap.ker (ϖ ^ i • (LinearMap.id : _ →ₗ[A] _))
      monotone' := fun i i' hii' q hq => by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hq ⊢
        rw [← Nat.add_sub_cancel' hii', pow_add, mul_comm, mul_smul, hq, smul_zero] }
  obtain ⟨n₀, hn₀⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) c
  have hbdd : ∀ (i : ℕ) (q : (↥K →ₗ[A] N) ⧸ R₀), n₀ ≤ i → ϖ ^ i • q = 0 → ϖ ^ n₀ • q = 0 := by
    intro i q hi hq
    have hmem : q ∈ c i := by
      show q ∈ LinearMap.ker (ϖ ^ i • (LinearMap.id : _ →ₗ[A] _))
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hq]
    rw [← hn₀ i hi] at hmem
    have : q ∈ LinearMap.ker (ϖ ^ n₀ • (LinearMap.id : _ →ₗ[A] _)) := hmem
    rwa [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this
  refine ⟨n₀, fun m k hmk g => ?_⟩
  have hn₀k : n₀ ≤ k := le_trans (Nat.le_add_left n₀ m) hmk
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (W N ϖ k).mkQ (LinearMap.comp g π) (Submodule.mkQ_surjective _)
  have hfK : ∀ κ : ↥K, f κ ∈ W N ϖ k := fun κ => by
    have := LinearMap.congr_fun hf κ
    rwa [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      show π (κ : Fin n → A) = 0 from LinearMap.mem_ker.mp κ.2, map_zero,
      Submodule.Quotient.mk_eq_zero] at this
  let eqv : N ≃ₗ[A] ↥(W N ϖ k) := LinearEquiv.ofInjective _ (pow_smul_injective ϖ hN k)
  have eqv_apply : ∀ w : N, ((eqv w : ↥(W N ϖ k)) : N) = ϖ ^ k • w := fun w => rfl
  let h : ↥K →ₗ[A] N := LinearMap.comp eqv.symm.toLinearMap ((LinearMap.comp f K.subtype).codRestrict (W N ϖ k) hfK)
  have hh : ∀ κ : ↥K, ϖ ^ k • h κ = f κ := fun κ => by
    rw [← eqv_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  have hcls : ϖ ^ k • R₀.mkQ h = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨f, LinearMap.ext fun κ => ?_⟩
    rw [resK_apply, LinearMap.smul_apply, hh]
  have hcls' := hbdd k _ hn₀k hcls
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hcls'
  obtain ⟨f', hf'⟩ := hcls'
  have hf'K : ∀ κ : ↥K, f' κ = ϖ ^ n₀ • h κ := fun κ => by
    have := LinearMap.congr_fun hf' κ
    rwa [resK_apply, LinearMap.smul_apply] at this
  let f₂ : (Fin n → A) →ₗ[A] N := f - ϖ ^ (k - n₀) • f'
  have hf₂K : K ≤ LinearMap.ker f₂ := fun y hy => by
    rw [LinearMap.mem_ker]
    show f y - ϖ ^ (k - n₀) • f' y = 0
    have h1 := hh ⟨y, hy⟩
    have h2 := hf'K ⟨y, hy⟩
    rw [h2, ← h1, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn₀k, sub_self]
  let ψ : M →ₗ[A] N := LinearMap.comp (K.liftQ f₂ hf₂K) (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ y : Fin n → A, ψ (π y) = f₂ y := fun y => by
    show K.liftQ f₂ hf₂K ((π.quotKerEquivOfSurjective hπ).symm (π y)) = f₂ y
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨ψ, fun v => ?_⟩
  obtain ⟨y, rfl⟩ := hπ v
  have hgy : g (π y) = (W N ϖ k).mkQ (f y) := by
    refine (LinearMap.congr_fun hf y).symm
  rw [hψ, hgy, Submodule.mkQ_apply, Submodule.mkQ_apply, red_mk]
  show Submodule.Quotient.mk (f y - ϖ ^ (k - n₀) • f' y) = Submodule.Quotient.mk (f y)
  rw [Submodule.Quotient.mk_sub, sub_eq_self, Submodule.Quotient.mk_eq_zero]
  have hmk : m ≤ k - n₀ := by omega
  refine W_anti ϖ hmk (pow_smul_mem_W ϖ _ _)

private lemma exists_surjective {A : Type u} [CommRing A] [IsNoetherianRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N] (ϖ : A) (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A)) (hN : ∀ n : N, ϖ • n = 0 → n = 0) (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ Nonempty ((M ⧸ W M ϖ k) ≃ₗ[A] (N ⧸ W N ϖ k))) : ∃ ψ : M →ₗ[A] N, Function.Surjective ψ := by
  obtain ⟨n₀, hn₀⟩ := exists_lift_const ϖ (M := M) hN
  obtain ⟨k, hk, ⟨e⟩⟩ := h (1 + n₀)
  obtain ⟨ψ, hψ⟩ := hn₀ 1 k hk (LinearMap.comp e.toLinearMap (W M ϖ k).mkQ)
  refine ⟨ψ, ?_⟩
  have hle : (⊤ : Submodule A N) ≤ LinearMap.range ψ ⊔ Ideal.span {ϖ} • ⊤ := by
    intro n _
    obtain ⟨q, hq⟩ := e.surjective ((W N ϖ k).mkQ n)
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
    have h1 := hψ v
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.mkQ_apply, red_mk, Submodule.Quotient.eq] at h1
    obtain ⟨w, hw⟩ := (mem_W ϖ).mp h1
    rw [pow_one] at hw
    have this : n = ψ v - ϖ • w := by rw [hw, sub_sub_cancel]
    rw [this]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self ψ v)) (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top))
  have hspan : Ideal.span {ϖ} ≤ Ideal.jacobson ⊥ := (Ideal.span_singleton_le_iff_mem _).mpr hϖ
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hspan hle
  rw [← LinearMap.range_eq_top]
  refine top_le_iff.mp htop

/--
[Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsNoetherianRing A]
  (ϖ : A)
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]
  -- given
  (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A))
  (hM : ∀ m : M, ϖ • m = 0 → m = 0)
  (hN : ∀ n : N, ϖ • n = 0 → n = 0)
  (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
    Nonempty ((M ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
      (N ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : N →ₗ[A] N))))) :
  -- imply
  Nonempty (M ≃ₗ[A] N) := by
  -- proof
  obtain ⟨ψ, hψ⟩ := exists_surjective ϖ hϖ hN h
  obtain ⟨χ, hχ⟩ := exists_surjective ϖ (M := N) (N := M) hϖ hM fun k₀ => by
    obtain ⟨k, hk, ⟨e⟩⟩ := h k₀
    refine ⟨k, hk, ⟨e.symm⟩⟩
  let _ : IsNoetherian A M := inferInstance
  have hinj : Function.Injective (LinearMap.comp χ ψ) :=
    IsNoetherian.injective_of_surjective_endomorphism _ (hχ.comp hψ)
  refine ⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp hinj, hψ⟩⟩


-- created on 2026-10-20
